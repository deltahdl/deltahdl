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
  void AddBlock(std::string_view name, bool name_is_generated,
                const std::vector<ModuleItem*>& body, bool has_begin_end,
                std::string_view prefix);
};

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
    if (sub->kind == ModuleItemKind::kModuleInst && !sub->inst_name.empty()) {
      const ModuleDecl* child = find_module(sub->inst_module);
      if (child != nullptr && child->decl_kind == ModuleDeclKind::kInterface) {
        std::string key = block_prefix + std::string(sub->inst_name);
        table.emplace(
            std::string_view(arena.AllocString(key.c_str(), key.size()),
                             key.size()),
            sub->inst_module);
      }
      continue;
    }
    AddConstruct(sub, block_prefix);
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

// A loop block's instances are stored under each iteration's index, which is
// not folded until the loop is elaborated, so a loop is not walked.
void BlockInterfaceWalk::AddConstruct(const ModuleItem* item,
                                      std::string_view prefix) {
  if (item->kind == ModuleItemKind::kGenerateIf) {
    AddIf(item, prefix);
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

// The actual `conn` is rewritten to, or null where it names no interface
// instance of a block or already names one by its stored name.
Expr* ResolvedActual(Expr* conn, const GenBlockPrefixes& prefixes,
                     const InterfaceInstTypes& table, const ScopeMap& scope,
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
  // `g.i` or `g[k].i`, an interface instance a generate block declares.
  std::optional<std::string> flat =
      FlattenBlockPath(conn->lhs, conn->rhs->text, scope);
  if (!flat) return nullptr;
  std::string_view key = FindBlockInterface(*flat, prefixes, table);
  if (key.empty()) return nullptr;
  return MakeInstanceIdent(key, conn, arena);
}

}  // namespace

void RegisterConditionalBlockInterfaces(
    const std::vector<ModuleItem*>& items,
    const std::function<const ModuleDecl*(std::string_view)>& find_module,
    InterfaceInstTypes& table, Arena& arena) {
  BlockInterfaceWalk walk{find_module, table, arena};
  for (const ModuleItem* item : items) walk.AddConstruct(item, {});
}

void ResolveGenBlockInterfaceActuals(RtlirModuleInst& inst,
                                     const InterfaceInstTypes& table,
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
