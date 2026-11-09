#include <cstddef>
#include <cstdint>
#include <format>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_params.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

namespace delta {

namespace {

void DropParamOverride(Elaborator::ParamList& child_params,
                       std::string_view pname) {
  Elaborator::ParamList kept;
  kept.reserve(child_params.size());
  for (const auto& e : child_params) {
    if (e.name != pname) kept.push_back(e);
  }
  child_params.swap(kept);
}

void ResetAllConfigParams(const ModuleDecl* child_decl,
                          Elaborator::ParamList& child_params,
                          std::vector<std::string_view>& locked) {
  child_params.clear();
  for (const auto& [dname, dexpr] : child_decl->params) {
    if (child_decl->localparam_port_names.count(dname) > 0) continue;
    if (child_decl->type_param_names.count(dname) > 0) continue;
    if (dexpr) {
      if (auto val = ConstEvalInt(dexpr)) {
        child_params.push_back({dname, *val, dexpr});
      }
    }
  }
  const std::vector<std::string_view> kOwned =
      OverridableParamNames(child_decl);
  locked.insert(locked.end(), kOwned.begin(), kOwned.end());
}

ScopeMap BuildConfigOverrideScope(const ScopeMap& parent_scope,
                                  const ScopeMap& config_localparam_scope) {
  ScopeMap scope = parent_scope;
  for (const auto& [name, val] : config_localparam_scope) {
    scope[name] = val;
  }
  return scope;
}

std::vector<std::string_view> MemberAccessNames(const Expr* e) {
  std::vector<std::string_view> names;
  while (e != nullptr && e->kind == ExprKind::kMemberAccess) {
    if (e->rhs == nullptr) return {};
    names.insert(names.begin(), e->rhs->text);
    e = e->lhs;
  }
  if (e == nullptr || e->kind != ExprKind::kIdentifier) return {};
  names.insert(names.begin(), e->text);
  return names;
}

const ScopeMap* AncestorScopeNamed(
    std::string_view scope_path, std::string_view parent_path,
    const ScopeMap& parent_scope,
    const std::unordered_map<std::string, ScopeMap>& ancestors) {
  const auto kNames = [scope_path](std::string_view path) {
    return path == scope_path ||
           (path.size() > scope_path.size() && path.ends_with(scope_path) &&
            path[path.size() - scope_path.size() - 1] == '.');
  };
  if (kNames(parent_path)) return &parent_scope;
  for (std::string_view path = parent_path;
       path.find('.') != std::string_view::npos;) {
    path = path.substr(0, path.rfind('.'));
    if (!kNames(path)) continue;
    auto it = ancestors.find(std::string(path));
    return it == ancestors.end() ? nullptr : &it->second;
  }
  return nullptr;
}

Expr* ResolveParentReference(
    Expr* e, std::string_view parent_path, const ScopeMap& parent_scope,
    const std::unordered_map<std::string, ScopeMap>& ancestors, Arena& arena) {
  if (e == nullptr) return e;
  if (e->kind == ExprKind::kSelect && e->base != nullptr &&
      e->base->kind == ExprKind::kMemberAccess) {
    Expr* base = ResolveParentReference(e->base, parent_path, parent_scope,
                                        ancestors, arena);
    if (base == e->base) return e;
    auto* copy = arena.Create<Expr>(*e);
    copy->base = base;
    return copy;
  }
  auto names = MemberAccessNames(e);
  if (names.size() < 2) return e;
  std::string scope_path;
  for (size_t i = 0; i + 1 < names.size(); ++i) {
    if (i > 0) scope_path += '.';
    scope_path.append(names[i]);
  }
  const ScopeMap* named =
      AncestorScopeNamed(scope_path, parent_path, parent_scope, ancestors);
  if (named == nullptr) return e;
  std::string_view param = names.back();
  if (auto it = named->find(param); it != named->end()) {
    auto* value = arena.Create<Expr>();
    value->kind = ExprKind::kIntegerLiteral;
    value->int_val = static_cast<uint64_t>(it->second);
    value->range = e->range;
    return value;
  }
  auto* ident = arena.Create<Expr>();
  ident->kind = ExprKind::kIdentifier;
  ident->text = param;
  ident->range = e->range;
  return ident;
}

std::vector<std::string_view> ApplyConfigOverrideParams(
    const ModuleDecl* child_decl,
    const std::vector<std::pair<std::string_view, Expr*>>& override_params,
    Elaborator::ParamList& child_params, const ScopeMap& scope,
    std::vector<std::string_view>& locked) {
  std::vector<std::string_view> unresolved;
  for (const auto& [pname, pexpr] : override_params) {
    DropParamOverride(child_params, pname);
    locked.push_back(pname);
    if (pexpr == nullptr || child_decl->type_param_names.contains(pname)) {
      continue;
    }
    if (!PushInstParamAssignment(child_decl, pname, pexpr, scope, child_params))
      unresolved.push_back(pname);
  }
  return unresolved;
}

void ReportUnappliedOverrides(const std::vector<std::string_view>& unapplied,
                              const ModuleDecl* child_decl, SourceLoc loc,
                              DiagEngine& diag) {
  for (std::string_view pname : unapplied) {
    diag.Error(loc,
               std::format("configuration override of parameter '{}' of '{}' "
                           "has no constant value",
                           pname, child_decl->name),
               Subclause("33.4.3"));
  }
}

}  // namespace

void Elaborator::ApplyConfigParamOverrides(
    const ModuleItem* item, const ModuleDecl* child_decl,
    Elaborator::ParamList& child_params, const ScopeMap& parent_scope,
    std::vector<std::string_view>& locked) {
  if (config_inst_path_.empty()) return;
  if (instance_param_overrides_.empty() && cell_param_overrides_.empty()) {
    return;
  }

  ScopeMap scope =
      BuildConfigOverrideScope(parent_scope, config_localparam_scope_);
  std::string_view parent_path = config_inst_path_;
  parent_path = parent_path.substr(0, parent_path.rfind('.'));
  if (parent_path != config_inst_path_) {
    config_ancestor_scopes_[std::string(parent_path)] = parent_scope;
  }
  auto apply = [&](const ConfigParamOverride& ov) {
    if (ov.reset_all) ResetAllConfigParams(child_decl, child_params, locked);
    auto params = ov.params;
    for (auto& assignment : params) {
      assignment.second =
          ResolveParentReference(assignment.second, parent_path, parent_scope,
                                 config_ancestor_scopes_, arena_);
    }
    ReportUnappliedOverrides(
        ApplyConfigOverrideParams(
            child_decl,
            AssignableConfigParams(child_decl, params, ov.loc, diag_),
            child_params, scope, locked),
        child_decl, ov.loc, diag_);
  };
  for (const auto& ov : cell_param_overrides_) {
    if (ov.inst_path == item->inst_module) apply(ov);
  }
  for (const auto& ov : instance_param_overrides_) {
    if (ov.inst_path == config_inst_path_) apply(ov);
  }
}

}  // namespace delta
