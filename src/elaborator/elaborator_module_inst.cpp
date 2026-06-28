#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <format>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

// §6.20.3: convert a type-parameter override argument (which the expression
// parser produces as a plain identifier, e.g. `shortint` or a class name `C`)
// into a DataType, via the shared name->type mapping.
static DataType TypeParamOverrideToDataType(const Expr* expr) {
  if (!expr || expr->kind != ExprKind::kIdentifier) return DataType{};
  return TypeNameToDataType(expr->text);
}

static bool InstParamsArePositional(const ModuleItem* item) {
  for (const auto& [n, e] : item->inst_params)
    if (n.empty() && e) return true;
  return false;
}

static const Expr* NamedTypeParamOverride(const ModuleItem* item,
                                          std::string_view pname) {
  for (const auto& [n, e] : item->inst_params)
    if (n == pname) return e;
  return nullptr;
}

// A positional override maps to the index of `pname` among the overridable
// (non-localparam) parameters, mirroring ResolvePositionalInstParams.
static const Expr* PositionalTypeParamOverride(const ModuleItem* item,
                                               const ModuleDecl* child_decl,
                                               std::string_view pname) {
  size_t idx = 0;
  for (const auto& [dname, dexpr] : child_decl->params) {
    if (child_decl->localparam_port_names.count(dname) > 0) continue;
    if (dname == pname)
      return idx < item->inst_params.size() ? item->inst_params[idx].second
                                            : nullptr;
    ++idx;
  }
  return nullptr;
}

// Locate the instantiation override expression for the type parameter `pname`,
// honoring both the named (.T(x)) and positional (#(x, ...)) forms (the two are
// never mixed -- the parser rejects that).
static const Expr* FindTypeParamOverrideExpr(const ModuleItem* item,
                                             const ModuleDecl* child_decl,
                                             std::string_view pname) {
  if (InstParamsArePositional(item))
    return PositionalTypeParamOverride(item, child_decl, pname);
  return NamedTypeParamOverride(item, pname);
}

// A saved typedef-map entry, so a type-parameter substitution made for one
// child elaboration can be undone afterwards (the map is shared across
// modules).
struct SavedTypedef {
  std::string_view name;
  bool existed = false;
  DataType prev;
};

// §6.20.3/§23.10: resolve each of the child's type parameters to a concrete
// type (an instantiation override if present, otherwise the declared default)
// and publish it in `typedefs` so the child's dependent declarations elaborate
// against the chosen type. A type parameter with neither a default nor an
// override is an error. Returns the prior entries so the caller can restore the
// shared map after the child is elaborated.
static std::vector<SavedTypedef> ApplyChildTypeParams(
    const ModuleItem* item, const ModuleDecl* child_decl, TypedefMap& typedefs,
    DiagEngine& diag) {
  std::vector<SavedTypedef> saved;
  for (size_t i = 0; i < child_decl->params.size(); ++i) {
    std::string_view pname = child_decl->params[i].first;
    if (child_decl->type_param_names.count(pname) == 0) continue;
    const Expr* ov = FindTypeParamOverrideExpr(item, child_decl, pname);
    bool has_default =
        i < child_decl->param_types.size() &&
        child_decl->param_types[i].kind != DataTypeKind::kImplicit;
    DataType resolved;
    if (ov && ov->kind == ExprKind::kIdentifier) {
      resolved = TypeParamOverrideToDataType(ov);
    } else if (has_default) {
      resolved = child_decl->param_types[i];
    } else {
      diag.Error(item->loc,
                 std::format("type parameter '{}' of '{}' has no default type "
                             "and no override at instantiation",
                             pname, child_decl->name));
      continue;
    }
    SavedTypedef s;
    s.name = pname;
    auto it = typedefs.find(pname);
    s.existed = it != typedefs.end();
    if (s.existed) s.prev = it->second;
    saved.push_back(s);
    typedefs[pname] = resolved;
  }
  return saved;
}

static void RestoreChildTypeParams(TypedefMap& typedefs,
                                   const std::vector<SavedTypedef>& saved) {
  for (const auto& s : saved) {
    if (s.existed)
      typedefs[s.name] = s.prev;
    else
      typedefs.erase(s.name);
  }
}

static uint32_t EvalInstDimSize(const Expr* left, const Expr* right) {
  if (left && right) {
    auto lv = ConstEvalInt(left);
    auto rv = ConstEvalInt(right);
    if (lv && rv) return static_cast<uint32_t>(std::abs(*lv - *rv) + 1);
  } else if (left) {
    auto v = ConstEvalInt(left);
    if (v && *v > 0) return static_cast<uint32_t>(*v);
  }
  return 0;
}

namespace {

// Removes any existing override for `pname` from `child_params`, preserving the
// relative order of the remaining entries.
void DropParamOverride(Elaborator::ParamList& child_params,
                       std::string_view pname) {
  Elaborator::ParamList kept;
  kept.reserve(child_params.size());
  for (const auto& e : child_params) {
    if (e.first != pname) kept.push_back(e);
  }
  child_params.swap(kept);
}

// "#()" returns every parameter to its module default: discard the
// instantiation's overrides and let the configuration own each one (§33.4.3).
void ResetAllConfigParams(const ModuleDecl* child_decl,
                          Elaborator::ParamList& child_params,
                          std::vector<std::string_view>& locked) {
  child_params.clear();
  for (const auto& [dname, dexpr] : child_decl->params) {
    if (child_decl->localparam_port_names.count(dname) > 0) continue;
    if (child_decl->type_param_names.count(dname) > 0) continue;
    locked.push_back(dname);
    if (dexpr) {
      if (auto val = ConstEvalInt(dexpr)) {
        child_params.push_back({dname, *val});
      }
    }
  }
}

// Resolves positional parameter overrides (#(v0, v1, ...)) against the child
// module's overridable parameters, appending evaluated values to child_params.
void ResolvePositionalInstParams(const ModuleItem* item,
                                 const ModuleDecl* child_decl,
                                 const ScopeMap& parent_scope,
                                 Elaborator::ParamList& child_params,
                                 DiagEngine& diag) {
  std::vector<std::string_view> targets;
  for (const auto& [dname, dexpr] : child_decl->params) {
    if (child_decl->localparam_port_names.count(dname) > 0) continue;
    targets.push_back(dname);
  }
  if (item->inst_params.size() > targets.size()) {
    diag.Error(item->loc,
               std::format("too many positional parameter overrides for module "
                           "'{}': {} provided, {} allowed",
                           item->inst_module, item->inst_params.size(),
                           targets.size()));
  }
  size_t n = std::min(item->inst_params.size(), targets.size());
  for (size_t i = 0; i < n; ++i) {
    auto* pexpr = item->inst_params[i].second;
    if (!pexpr) continue;
    auto val = ConstEvalInt(pexpr, parent_scope);
    if (val) child_params.push_back({targets[i], *val});
  }
}

// Resolves named parameter overrides (#(.p(v), ...)) against the child module's
// overridable parameters, appending evaluated values to child_params.
void ResolveNamedInstParams(const ModuleItem* item,
                            const ModuleDecl* child_decl,
                            const ScopeMap& parent_scope,
                            Elaborator::ParamList& child_params,
                            DiagEngine& diag) {
  std::unordered_set<std::string_view> overridable;
  for (const auto& [dname, dexpr] : child_decl->params) {
    if (child_decl->localparam_port_names.count(dname) > 0) continue;
    overridable.insert(dname);
  }
  for (const auto& [pname, pexpr] : item->inst_params) {
    if (overridable.count(pname) == 0) {
      diag.Error(item->loc, std::format("module '{}' has no parameter '{}'",
                                        item->inst_module, pname));
      continue;
    }
    if (!pexpr) continue;
    auto val = ConstEvalInt(pexpr, parent_scope);
    if (val) child_params.push_back({pname, *val});
  }
}

// Marks each parameter the configuration fixed so a later defparam cannot
// change it: a config override takes precedence over defparam (§33.4.3).
void MarkConfigLockedParams(
    RtlirModuleInst& inst, const std::vector<std::string_view>& config_locked) {
  if (!inst.resolved) return;
  for (auto pname : config_locked) {
    for (auto& p : inst.resolved->params) {
      if (p.name == pname) {
        p.config_locked = true;
        break;
      }
    }
  }
}

// Evaluates the instance array dimensions, appending each nonzero size to
// inst_dim_sizes and returning the product (total instance count, default 1).
uint32_t ComputeInstDimSizes(const ModuleItem* item,
                             std::vector<uint32_t>& inst_dim_sizes) {
  uint32_t total_instances = 1;
  for (const auto& [left, right] : item->inst_dims) {
    uint32_t sz = EvalInstDimSize(left, right);
    if (sz > 0) {
      inst_dim_sizes.push_back(sz);
      total_instances *= sz;
    }
  }
  return total_instances;
}

// Returns true when the instantiation supplied at least one positional
// (unnamed) parameter override (#(v0, v1, ...)).
bool InstUsesPositionalParams(const ModuleItem* item) {
  for (const auto& [pname, pexpr] : item->inst_params) {
    if (pname.empty() && pexpr) return true;
  }
  return false;
}

// Reports a diagnostic for an instantiation of an unknown module, qualifying
// the name with its scope when one was specified.
void ReportUnknownModule(const ModuleItem* item, DiagEngine& diag) {
  if (item->inst_scope.empty())
    diag.Error(item->loc,
               std::format("unknown module '{}'", item->inst_module));
  else
    diag.Error(item->loc, std::format("unknown module '{}::{}'",
                                      item->inst_scope, item->inst_module));
}

// Resolves the instantiation's own parameter overrides into child_params,
// dispatching on whether they were written positionally or by name.
void ResolveInstParams(const ModuleItem* item, const ModuleDecl* child_decl,
                       const ScopeMap& parent_scope,
                       Elaborator::ParamList& child_params, DiagEngine& diag) {
  if (InstUsesPositionalParams(item)) {
    ResolvePositionalInstParams(item, child_decl, parent_scope, child_params,
                                diag);
  } else {
    ResolveNamedInstParams(item, child_decl, parent_scope, child_params, diag);
  }
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

// Applies one configuration override's explicit per-parameter values onto
// child_params, recording each touched parameter in `locked`. A present
// expression sets a new value, a null one ("(.p())") leaves the parameter at
// its module default; either way the configuration now owns the parameter
// (§33.4.3).
void ApplyConfigOverrideParams(
    const std::vector<std::pair<std::string_view, Expr*>>& override_params,
    Elaborator::ParamList& child_params, const ScopeMap& scope,
    std::vector<std::string_view>& locked) {
  for (const auto& [pname, pexpr] : override_params) {
    DropParamOverride(child_params, pname);
    if (pexpr) {
      if (auto val = ConstEvalInt(pexpr, scope)) {
        child_params.push_back({pname, *val});
      }
    }
    locked.push_back(pname);
  }
}

}  // namespace

void Elaborator::ApplyConfigParamOverrides(
    const ModuleDecl* child_decl, Elaborator::ParamList& child_params,
    const ScopeMap& parent_scope, std::vector<std::string_view>& locked) {
  if (instance_param_overrides_.empty() || current_inst_path_.empty()) return;

  // Parameter identifiers resolve in the instance's parent scope, augmented
  // with the configuration's own localparams (§33.4.3).
  ScopeMap scope =
      BuildConfigOverrideScope(parent_scope, config_localparam_scope_);

  for (const auto& ov : instance_param_overrides_) {
    if (ov.inst_path != current_inst_path_) continue;

    if (ov.reset_all) {
      ResetAllConfigParams(child_decl, child_params, locked);
    }
    ApplyConfigOverrideParams(ov.params, child_params, scope, locked);
  }
}

void Elaborator::ElaborateModuleInst(ModuleItem* item, RtlirModule* mod) {
  if (!item->inst_name.empty() &&
      !declared_names_.insert(item->inst_name).second) {
    diag_.Error(item->loc,
                std::format("redeclaration of '{}'", item->inst_name));
  }
  RtlirModuleInst inst;
  inst.module_name = item->inst_module;
  inst.inst_name = item->inst_name;

  std::string saved_inst_path = current_inst_path_;
  if (!current_inst_path_.empty()) current_inst_path_.push_back('.');
  current_inst_path_.append(item->inst_name.data(), item->inst_name.size());

  auto* child_decl = FindModuleInScope(item->inst_module);
  if (!child_decl) {
    ReportUnknownModule(item, diag_);
    mod->children.push_back(inst);
    current_inst_path_ = std::move(saved_inst_path);
    return;
  }

  auto saved_nested = nested_module_decls_;
  Elaborator::ParamList child_params;
  auto parent_scope = BuildParamScope(mod);

  ResolveInstParams(item, child_decl, parent_scope, child_params, diag_);

  // A configuration may override (or reset) this instance's parameters on top
  // of whatever the instantiation specified (§33.4.3).
  std::vector<std::string_view> config_locked;
  ApplyConfigParamOverrides(child_decl, child_params, parent_scope,
                            config_locked);

  // §6.20.3/§23.10: publish the child's type-parameter substitutions into the
  // shared typedef map so its dependent declarations resolve against the chosen
  // types, then restore the map once the child has been elaborated.
  auto saved_type_params =
      ApplyChildTypeParams(item, child_decl, typedefs_, diag_);
  inst.resolved = ElaborateModule(child_decl, child_params);
  RestoreChildTypeParams(typedefs_, saved_type_params);
  nested_module_decls_ = std::move(saved_nested);

  MarkConfigLockedParams(inst, config_locked);
  BindPorts(inst, item, mod, child_decl);

  std::vector<uint32_t> inst_dim_sizes;
  uint32_t total_instances = ComputeInstDimSizes(item, inst_dim_sizes);

  if (!item->inst_dims.empty()) {
    ValidateInstanceArrayPorts(inst, item, mod, inst_dim_sizes,
                               total_instances);
  } else {
    ValidateUnpackedArrayPorts(inst, item, mod);
  }

  CheckPortCoercion(inst, item->loc);
  CheckUwirePortMerge(inst, item, mod);
  CheckInterconnectPortMerge(inst, item, mod);

  inst.attrs = ResolveAttributes(item->attrs, diag_);
  mod->children.push_back(inst);
  current_inst_path_ = std::move(saved_inst_path);
}

}  // namespace delta
