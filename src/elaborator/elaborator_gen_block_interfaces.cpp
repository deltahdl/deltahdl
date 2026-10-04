// §25.3 with §27.4 and §27.5: an interface port connected to an interface
// instance a generate block declares, written in the block or reached through
// it by a hierarchical name.

#include "elaborator/elaborator_gen_block_interfaces.h"

#include <cstdint>
#include <format>
#include <functional>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

namespace delta {

std::string_view FindBlockInterface(std::string_view name,
                                    const GenBlockPrefixes& prefixes,
                                    const InterfaceInstTypes& table) {
  for (auto it = prefixes.rbegin(); it != prefixes.rend(); ++it) {
    std::string key = std::string(*it) + std::string(name);
    auto found = table.find(key);
    if (found != table.end()) return found->first;
  }
  auto found = table.find(name);
  return found != table.end() ? found->first : std::string_view{};
}

namespace {

struct BlockInterfaceWalk {
  const std::function<const ModuleDecl*(std::string_view)>& find_module;
  InterfaceInstTypes& table;
  Arena& arena;

  void AddConstruct(const ModuleItem* item, std::string_view prefix);
  void AddIf(const ModuleItem* item, std::string_view prefix);
  void AddLoop(const ModuleItem* item, std::string_view prefix);
  bool AddInterfaceInstance(const ModuleItem* item, std::string_view prefix);
  void AddBlock(std::string_view name, bool name_is_generated,
                const std::vector<ModuleItem*>& body, bool has_begin_end,
                std::string_view prefix);
};

// Registers `item` under `prefix` followed by its name where it is an instance
// of an interface; false where it is no instance at all.
bool BlockInterfaceWalk::AddInterfaceInstance(const ModuleItem* item,
                                              std::string_view prefix) {
  if (item->kind != ModuleItemKind::kModuleInst || item->inst_name.empty()) {
    return false;
  }
  const ModuleDecl* child = find_module(item->inst_module);
  if (child != nullptr && child->decl_kind == ModuleDeclKind::kInterface) {
    std::string key = std::string(prefix) + std::string(item->inst_name);
    table.emplace(std::string_view(arena.AllocString(key.c_str(), key.size()),
                                   key.size()),
                  item->inst_module);
  }
  return true;
}

// One block of a conditional construct. ElaborateConditionalGenerateBlock
// stores what a block declares under the enclosing prefix followed by the
// block's name and `_`, and gives a directly nested construct's blocks
// (§27.5) the enclosing prefix itself. A block §27.6 named is left out, since
// §23.6 lets no path written outside it reach in.
void BlockInterfaceWalk::AddBlock(std::string_view name, bool name_is_generated,
                                  const std::vector<ModuleItem*>& body,
                                  bool has_begin_end, std::string_view prefix) {
  if (IsDirectlyNestedBlock(body, has_begin_end)) {
    AddConstruct(body[0], prefix);
    return;
  }
  if (name.empty() || name_is_generated) return;
  std::string block_prefix = std::format("{}{}_", prefix, name);
  for (const ModuleItem* sub : body) {
    if (!AddInterfaceInstance(sub, block_prefix))
      AddConstruct(sub, block_prefix);
  }
}

// §27.4: a named loop block is an array of block instances, each stored under
// the enclosing prefix, the block's name and the iteration's index, which is
// folded only when the loop is elaborated. An interface instance the block
// declares is therefore registered under the block's name followed by `[]_`,
// which no stored name can spell, for `g[k].i` to be resolved through once its
// index is folded (LoopBlockInstance). A construct nested in the loop block is
// stored under the index as well, and is not walked.
void BlockInterfaceWalk::AddLoop(const ModuleItem* item,
                                 std::string_view prefix) {
  if (item->name.empty() || item->name_is_generated) return;
  std::string template_prefix = std::format("{}{}[]_", prefix, item->name);
  for (const ModuleItem* sub : item->gen_body) {
    AddInterfaceInstance(sub, template_prefix);
  }
}

void BlockInterfaceWalk::AddIf(const ModuleItem* item,
                               std::string_view prefix) {
  AddBlock(item->name, item->name_is_generated, item->gen_body,
           item->gen_body_has_begin_end, prefix);
  const ModuleItem* other = item->gen_else;
  if (other == nullptr) return;
  if (other->gen_cond != nullptr) {
    AddIf(other, prefix);
    return;
  }
  AddBlock(other->name, other->name_is_generated, other->gen_body,
           other->gen_body_has_begin_end, prefix);
}

void BlockInterfaceWalk::AddConstruct(const ModuleItem* item,
                                      std::string_view prefix) {
  if (item->kind == ModuleItemKind::kGenerateIf) {
    AddIf(item, prefix);
    return;
  }
  if (item->kind == ModuleItemKind::kGenerateFor) {
    AddLoop(item, prefix);
    return;
  }
  if (item->kind != ModuleItemKind::kGenerateCase) return;
  for (const auto& ci : item->gen_case_items) {
    AddBlock(ci.label, ci.name_is_generated, ci.body, ci.has_begin_end, prefix);
  }
}

Expr* MakeInstanceIdent(std::string_view key, const Expr* from, Arena& arena) {
  auto* ident = arena.Create<Expr>();
  ident->kind = ExprKind::kIdentifier;
  ident->text = key;
  ident->range = from->range;
  return ident;
}

// The stored name of the interface instance `g.i` or `g[k].i` reaches: the
// block's prefix as ElaborateConditionalGenerateBlock and
// ElaborateGenerateFor build it, followed by the instance's name.
std::optional<std::string> FlattenBlockPath(const Expr* head,
                                            std::string_view member,
                                            const ScopeMap& scope) {
  if (head->kind == ExprKind::kIdentifier) {
    return std::format("{}_{}", head->text, member);
  }
  if (head->kind != ExprKind::kSelect || head->base == nullptr ||
      head->base->kind != ExprKind::kIdentifier || head->index == nullptr ||
      head->index_end != nullptr) {
    return std::nullopt;
  }
  std::optional<int64_t> index = ConstEvalInt(head->index, scope);
  if (!index) return std::nullopt;
  return std::format("{}_{}_{}", head->base->text, *index, member);
}

// The stored name of the instance the path `conn`, `g[k].i`, names in a loop
// block, whose stored name `flat` is registered only once the loop is
// elaborated: found through the block's `g[]_i` entry
// (BlockInterfaceWalk::AddLoop) and entered into `table` for the interface
// checks to find. Empty where no loop block named `g` declares an interface
// instance `i`.
std::string_view LoopBlockInstance(const Expr* conn, const std::string& flat,
                                   const GenBlockPrefixes& prefixes,
                                   InterfaceInstTypes& table, Arena& arena) {
  if (conn->lhs->kind != ExprKind::kSelect) return {};
  std::string pattern =
      std::format("{}[]_{}", conn->lhs->base->text, conn->rhs->text);
  std::string_view found = FindBlockInterface(pattern, prefixes, table);
  if (found.empty()) return {};
  std::string key =
      std::string(found.substr(0, found.size() - pattern.size())) + flat;
  std::string_view stored(arena.AllocString(key.c_str(), key.size()),
                          key.size());
  table.emplace(stored, table.at(found));
  return stored;
}

// The actual `g.i` or `g[k].i` is rewritten to, an interface instance a
// generate block declares, or null where it names none.
Expr* ResolvedPath(Expr* conn, const GenBlockPrefixes& prefixes,
                   InterfaceInstTypes& table, const ScopeMap& scope,
                   Arena& arena) {
  std::optional<std::string> flat =
      FlattenBlockPath(conn->lhs, conn->rhs->text, scope);
  if (!flat) return nullptr;
  std::string_view key = FindBlockInterface(*flat, prefixes, table);
  if (key.empty()) {
    key = LoopBlockInstance(conn, *flat, prefixes, table, arena);
  }
  if (key.empty()) return nullptr;
  return MakeInstanceIdent(key, conn, arena);
}

// The actual `conn` is rewritten to, or null where it names no interface
// instance of a block or already names one by its stored name.
Expr* ResolvedActual(Expr* conn, const GenBlockPrefixes& prefixes,
                     InterfaceInstTypes& table, const ScopeMap& scope,
                     Arena& arena) {
  if (conn->kind == ExprKind::kIdentifier) {
    std::string_view key = FindBlockInterface(conn->text, prefixes, table);
    if (key.empty() || key == conn->text) return nullptr;
    return MakeInstanceIdent(key, conn, arena);
  }
  if (conn->kind != ExprKind::kMemberAccess || conn->is_scope_resolution ||
      conn->lhs == nullptr || conn->rhs == nullptr ||
      conn->rhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  // `i.mp`, a modport of an interface instance (§25.5).
  if (conn->lhs->kind == ExprKind::kIdentifier) {
    std::string_view key = FindBlockInterface(conn->lhs->text, prefixes, table);
    if (key == conn->lhs->text) return nullptr;
    if (!key.empty()) {
      auto* copy = arena.Create<Expr>(*conn);
      copy->lhs = MakeInstanceIdent(key, conn->lhs, arena);
      return copy;
    }
  }
  return ResolvedPath(conn, prefixes, table, scope, arena);
}

}  // namespace

void EnterGenBlockInstance(RtlirModuleInst& inst, const ModuleDecl* child_decl,
                           const GenBlockContext& context,
                           InterfaceInstTypes& table) {
  inst.gen_block_path = context.path;
  inst.gen_block_consts = context.consts;
  inst.gen_block_prefixes = context.prefixes;
  if (child_decl->decl_kind == ModuleDeclKind::kInterface &&
      !context.prefixes.empty()) {
    table.emplace(inst.inst_name, child_decl->name);
  }
}

void RegisterGenerateBlockInterfaces(
    const std::vector<ModuleItem*>& items,
    const std::function<const ModuleDecl*(std::string_view)>& find_module,
    InterfaceInstTypes& table, Arena& arena) {
  BlockInterfaceWalk walk{find_module, table, arena};
  for (const ModuleItem* item : items) walk.AddConstruct(item, {});
}

void ResolveGenBlockInterfaceActuals(RtlirModuleInst& inst,
                                     InterfaceInstTypes& table,
                                     const ScopeMap& scope, Arena& arena) {
  // Every binding is asked rather than only those of a port marked an
  // interface port: an actual is rewritten only where it names an entry of
  // `table`, which holds interface instances alone, and the mark is not set on
  // every interface port by the time the bindings are made.
  for (RtlirPortBinding& binding : inst.port_bindings) {
    if (binding.connection == nullptr) continue;
    if (Expr* actual = ResolvedActual(
            binding.connection, inst.gen_block_prefixes, table, scope, arena)) {
      binding.connection = actual;
    }
  }
}

}  // namespace delta
