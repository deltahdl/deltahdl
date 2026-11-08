#include "elaborator/elaborator_gen_block_interfaces.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <format>
#include <functional>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
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

Expr* ResolvedActual(Expr* conn, const GenBlockPrefixes& prefixes,
                     const InterfaceActualScope& scope, bool& through_block) {
  if (conn->kind == ExprKind::kIdentifier) {
    std::string_view key =
        FindBlockInterface(conn->text, prefixes, scope.table);
    if (key.empty() || key == conn->text) return nullptr;
    return MakeInstanceIdent(key, conn, scope.arena);
  }
  if (conn->kind != ExprKind::kMemberAccess || conn->is_scope_resolution ||
      conn->lhs == nullptr || conn->rhs == nullptr ||
      conn->rhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  if (conn->lhs->kind == ExprKind::kIdentifier) {
    std::string_view key =
        FindBlockInterface(conn->lhs->text, prefixes, scope.table);
    if (key == conn->lhs->text) return nullptr;
    if (!key.empty()) {
      auto* copy = scope.arena.Create<Expr>(*conn);
      copy->lhs = MakeInstanceIdent(key, conn->lhs, scope.arena);
      return copy;
    }
  }
  through_block = ResolvedPath(conn, prefixes, scope.table, scope.params,
                               scope.arena) != nullptr;
  return nullptr;
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
                                     const InterfaceActualScope& scope) {
  for (RtlirPortBinding& binding : inst.port_bindings) {
    if (binding.connection == nullptr) continue;
    bool through_block = false;
    if (Expr* actual =
            ResolvedActual(binding.connection, inst.gen_block_prefixes, scope,
                           through_block)) {
      binding.connection = actual;
    }
    if (!through_block) continue;
    scope.diag.Error(scope.loc,
                     std::format("the actual of interface port '{}' resolves "
                                 "through a generate block",
                                 binding.port_name),
                     Subclause("25.3"));
    binding.refused_actual = true;
  }
}

namespace {

struct ActualPathStep {
  std::string_view name;
  bool indexed = false;
};

void AppendActualPathSteps(const Expr* e, std::vector<ActualPathStep>& steps) {
  if (e->kind == ExprKind::kMemberAccess) {
    AppendActualPathSteps(e->lhs, steps);
    AppendActualPathSteps(e->rhs, steps);
    return;
  }
  bool indexed = e->kind == ExprKind::kSelect;
  steps.push_back({indexed ? e->base->text : e->text, indexed});
}

const ModuleItem* FindInstanceItem(const ModuleDecl* decl,
                                   std::string_view name) {
  for (const ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kModuleInst && item->inst_name == name)
      return item;
  }
  return nullptr;
}

bool BindsInterfacePort(const RtlirModuleInst& inst, std::string_view name) {
  for (const RtlirPort& port : inst.resolved->ports) {
    if (port.name == name && port.is_interface_port) return true;
  }
  return false;
}

void RewriteInstancePath(RtlirPortBinding& binding, const std::string& path,
                         std::string_view type, size_t rest,
                         const InterfaceActualScope& scope) {
  std::string_view key(scope.arena.AllocString(path.c_str(), path.size()),
                       path.size());
  scope.table.emplace(key, type);
  Expr* conn = binding.connection;
  if (rest == 1) {
    binding.connection = MakeInstanceIdent(key, conn, scope.arena);
    return;
  }
  auto* copy = scope.arena.Create<Expr>(*conn);
  copy->lhs = MakeInstanceIdent(key, conn->lhs, scope.arena);
  binding.connection = copy;
}

struct PathStart {
  const ModuleDecl* decl;
  size_t step;
  std::string path;
};

PathStart StartOfPath(const InterfaceActualScope& scope,
                      const std::vector<ActualPathStep>& steps) {
  const ActualPathStep& first = steps.front();
  if (first.indexed || FindInstanceItem(scope.parent, first.name) != nullptr) {
    return {scope.parent, 0, {}};
  }
  if (first.name == scope.parent->name) return {scope.parent, 1, {}};
  auto top = std::ranges::find(scope.tops, first.name, &ModuleDecl::name);
  if (top == scope.tops.end()) return {scope.parent, 0, {}};
  return {*top, 1, std::string(first.name) + "."};
}

void ResolveInstancePath(RtlirPortBinding& binding,
                         const std::vector<ActualPathStep>& steps,
                         const InterfaceActualScope& scope) {
  PathStart start = StartOfPath(scope, steps);
  const ModuleDecl* decl = start.decl;
  std::string path = std::move(start.path);
  for (size_t k = start.step; k < steps.size(); ++k) {
    const ModuleItem* item = FindInstanceItem(decl, steps[k].name);
    decl = item == nullptr ? nullptr : scope.find_module(item->inst_module);
    if (decl == nullptr) return;
    bool arrayed = steps[k].indexed || !item->inst_dims.empty();
    path += steps[k].name;
    size_t rest = steps.size() - k;
    if (decl->decl_kind == ModuleDeclKind::kInterface) {
      if (k == 0 || arrayed || rest > 2) return;
      RewriteInstancePath(binding, path, decl->name, rest, scope);
      return;
    }
    if (arrayed) {
      scope.diag.Error(scope.loc,
                       std::format("the actual of interface port '{}' "
                                   "resolves through the arrayed instance "
                                   "'{}'",
                                   binding.port_name, path),
                       Subclause("25.3"));
      binding.refused_actual = true;
      return;
    }
    path += '.';
  }
}

}  // namespace

void ResolveInstancePathActuals(RtlirModuleInst& inst,
                                const InterfaceActualScope& scope) {
  for (RtlirPortBinding& binding : inst.port_bindings) {
    if (binding.connection == nullptr ||
        !BindsInterfacePort(inst, binding.port_name)) {
      continue;
    }
    std::vector<ActualPathStep> steps;
    AppendActualPathSteps(binding.connection, steps);
    if (steps.size() > 1) ResolveInstancePath(binding, steps, scope);
  }
}

}  // namespace delta
