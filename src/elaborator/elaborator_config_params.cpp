// §33.4.3's parameter overrides, applied to an instance as a configuration's
// instance or cell clause writes them.

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
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_params.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

namespace delta {

namespace {

// Removes any existing override for `pname` from `child_params`, preserving the
// relative order of the remaining entries.
void DropParamOverride(Elaborator::ParamList& child_params,
                       std::string_view pname) {
  Elaborator::ParamList kept;
  kept.reserve(child_params.size());
  for (const auto& e : child_params) {
    if (e.name != pname) kept.push_back(e);
  }
  child_params.swap(kept);
}

// "#()" returns every parameter to its module default: discard the
// instantiation's overrides and let the configuration own each one (§33.4.3).
//
// §33.4.3 (printed page 940) has the configuration's parameter override take
// precedence over a defparam on the same parameter, and the parameters the
// use clause returns to their defaults are every one the instance's
// assignment could name (OverridableParamNames) -- a `parameter` among the
// items of a module declared with no parameter port list among them
// (§6.20.1, printed 125-126), which the cleared assignment list leaves to
// its own value. The parameter port list's alone were locked before, so
// `defparam top.u.P = 9` in top after `instance top.u use #()` on `module c;
// parameter P = 2;` made P 9. A defparam on a type parameter is refused
// before the lock is read (§6.20.3), so locking one changes nothing.
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

// Builds the scope used to evaluate configuration parameter-override
// expressions: the instance's parent scope augmented with the configuration's
// own localparams (§33.4.3).
ScopeMap BuildConfigOverrideScope(const ScopeMap& parent_scope,
                                  const ScopeMap& config_localparam_scope) {
  ScopeMap scope = parent_scope;
  for (const auto& [name, val] : config_localparam_scope) {
    scope[name] = val;
  }
  return scope;
}

// The dotted names a member-access chain is written with, outermost first, or
// nothing where the chain is not a pure one.
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

// The parameter values of the instance `scope_path` names, read upward from
// the configured instance's parent at `parent_path` as a bind statement's
// names are (§33.4.3): the parent itself, or an instance above it whose path
// is `scope_path` or ends in it. Null where none is.
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

// §33.4.3 (printed page 940): parameter identifiers resolve starting in the
// instance's parent scope and upward from it, so a hierarchical reference in a
// configuration's override that names the configured instance's parent,
// `top.WIDTH` for `instance top.a1`, or an instance above it, `top.WIDTH` for
// `instance top.a1.b`, is that instance's parameter. It is folded here, where
// those values are known: a scalar parameter becomes its value and a
// parameter array its name in the parent's scope, which an index -- a literal
// or a config localparam -- then selects in. A reference naming any other scope
// is left as it was written.
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

// Applies one configuration override's explicit per-parameter values onto
// child_params, recording each touched parameter in `locked`. A present
// expression sets a new value, a null one ("(.p())") leaves the parameter at
// its module default; either way the configuration now owns the parameter
// (§33.4.3). A value is taken as an instantiation's assignment of the same
// parameter is (PushInstParamAssignment), so a real, an array, a structure or
// a type reaches the instance as it would there; a type parameter of the
// parameter port list is given its type by ApplyChildTypeParams instead.
// Returns the parameters whose value gave nothing, which §33.4.3's constant
// value leaves no way to apply.
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
    const std::size_t kBefore = child_params.size();
    PushInstParamAssignment(child_decl, pname, pexpr, scope, child_params);
    if (child_params.size() == kBefore) unresolved.push_back(pname);
  }
  return unresolved;
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

  // Parameter identifiers resolve in the instance's parent scope, augmented
  // with the configuration's own localparams (§33.4.3).
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
    for (std::string_view pname : ApplyConfigOverrideParams(
             child_decl,
             AssignableConfigParams(child_decl, params, ov.loc, diag_),
             child_params, scope, locked)) {
      diag_.Error(ov.loc,
                  std::format("configuration override of parameter '{}' of "
                              "'{}' has no constant value",
                              pname, child_decl->name),
                  Subclause("33.4.3"));
    }
  };
  // §33.4.1.4: a cell clause's overrides reach every instance of the cell; an
  // instance clause, the more specific selection (§33.4.1.6), is applied after
  // it and so decides a parameter both name.
  for (const auto& ov : cell_param_overrides_) {
    if (ov.inst_path == item->inst_module) apply(ov);
  }
  for (const auto& ov : instance_param_overrides_) {
    if (ov.inst_path == config_inst_path_) apply(ov);
  }
}

}  // namespace delta
