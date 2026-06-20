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
#include "parser/ast.h"

namespace delta {

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
    (void)dexpr;
    if (child_decl->localparam_port_names.count(dname) > 0) continue;
    if (child_decl->type_param_names.count(dname) > 0) continue;
    locked.push_back(dname);
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

}  // namespace

void Elaborator::ApplyConfigParamOverrides(
    const ModuleDecl* child_decl, Elaborator::ParamList& child_params,
    const ScopeMap& parent_scope, std::vector<std::string_view>& locked) {
  if (instance_param_overrides_.empty() || current_inst_path_.empty()) return;

  // Parameter identifiers resolve in the instance's parent scope, augmented
  // with the configuration's own localparams (§33.4.3).
  ScopeMap scope = parent_scope;
  for (const auto& [name, val] : config_localparam_scope_) {
    scope[name] = val;
  }

  for (const auto& ov : instance_param_overrides_) {
    if (ov.inst_path != current_inst_path_) continue;

    if (ov.reset_all) {
      ResetAllConfigParams(child_decl, child_params, locked);
    }

    for (const auto& [pname, pexpr] : ov.params) {
      // Replace any value the instantiation supplied; a present expression sets
      // a new value while a null one ("(.p())") leaves the parameter at its
      // module default. Either way the configuration now owns the parameter.
      DropParamOverride(child_params, pname);
      if (pexpr) {
        if (auto val = ConstEvalInt(pexpr, scope)) {
          child_params.push_back({pname, *val});
        }
      }
      locked.push_back(pname);
    }
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
    if (item->inst_scope.empty())
      diag_.Error(item->loc,
                  std::format("unknown module '{}'", item->inst_module));
    else
      diag_.Error(item->loc, std::format("unknown module '{}::{}'",
                                         item->inst_scope, item->inst_module));
    mod->children.push_back(inst);
    current_inst_path_ = std::move(saved_inst_path);
    return;
  }

  auto saved_nested = nested_module_decls_;
  Elaborator::ParamList child_params;
  auto parent_scope = BuildParamScope(mod);

  bool is_positional = false;
  for (const auto& [pname, pexpr] : item->inst_params) {
    if (pname.empty() && pexpr) {
      is_positional = true;
      break;
    }
  }

  if (is_positional) {
    ResolvePositionalInstParams(item, child_decl, parent_scope, child_params,
                                diag_);
  } else {
    ResolveNamedInstParams(item, child_decl, parent_scope, child_params, diag_);
  }

  // A configuration may override (or reset) this instance's parameters on top
  // of whatever the instantiation specified (§33.4.3).
  std::vector<std::string_view> config_locked;
  ApplyConfigParamOverrides(child_decl, child_params, parent_scope,
                            config_locked);

  inst.resolved = ElaborateModule(child_decl, child_params);
  nested_module_decls_ = std::move(saved_nested);

  MarkConfigLockedParams(inst, config_locked);
  BindPorts(inst, item, mod);

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
