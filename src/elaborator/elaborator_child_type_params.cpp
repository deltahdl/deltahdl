#include "elaborator/elaborator_child_type_params.h"

#include <algorithm>
#include <cstddef>
#include <format>
#include <optional>
#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/type_eval.h"
#include "elaborator/type_param_restriction.h"
#include "elaborator/type_parameter_values.h"
#include "elaborator/unpacked_array_type.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

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

static const Expr* FindTypeParamOverrideExpr(const ModuleItem* item,
                                             const ModuleDecl* child_decl,
                                             std::string_view pname) {
  if (InstParamsArePositional(item))
    return PositionalTypeParamOverride(item, child_decl, pname);
  return NamedTypeParamOverride(item, pname);
}

static const Expr* ConfigTypeParamOverride(const TypeParamAssignments& from,
                                           std::string_view pname) {
  for (const auto& [name, expr] : from.config) {
    if (name == pname) return expr;
  }
  return nullptr;
}

struct ChildTypeParamBinding {
  AssignedType type;
  const Expr* override_expr = nullptr;
};

bool TypeParamPortHasDefault(const DataType& type) {
  return type.kind != DataTypeKind::kImplicit || type.type_ref_expr != nullptr;
}

DataType InInstantiatingScope(DataType dt, const TypedefMap& typedefs) {
  while (dt.kind == DataTypeKind::kNamed && dt.scope_name.empty() &&
         dt.packed_dim_left == nullptr) {
    auto it = typedefs.find(dt.type_name);
    if (it == typedefs.end()) break;
    const std::string_view kName = dt.type_name;
    dt = it->second;
    if (dt.kind == DataTypeKind::kEnum && dt.type_name.empty())
      dt.type_name = kName;
  }
  return dt;
}

static bool NamesAnEarlierTypeParam(const DataType& type,
                                    const ModuleDecl* child_decl, size_t i) {
  if (type.kind != DataTypeKind::kNamed || !type.scope_name.empty())
    return false;
  for (size_t k = 0; k < i; ++k) {
    if (child_decl->params[k].first == type.type_name) return true;
  }
  return false;
}

static AssignedType DefaultChildType(const TypeParamAssignments& from,
                                     const ModuleDecl* child_decl, size_t i) {
  const DataType& type = child_decl->param_types.at(i);
  if (NamesAnEarlierTypeParam(type, child_decl, i)) return {type, {type, {}}};
  return {type, from.default_type(type)};
}

static std::optional<ChildTypeParamBinding> ResolveChildTypeParam(
    const TypeParamAssignments& from, const ModuleDecl* child_decl, size_t i,
    DiagEngine& diag) {
  const ModuleItem* item = from.item;
  std::string_view pname = child_decl->params[i].first;
  const Expr* ov = ConfigTypeParamOverride(from, pname);
  const bool kConfigReset =
      from.config_reset_all ||
      std::ranges::find(from.config_reset, pname) != from.config_reset.end();
  if (ov == nullptr && !kConfigReset) {
    ov = FindTypeParamOverrideExpr(item, child_decl, pname);
  }
  if (ov != nullptr) {
    AssignedType assigned = from.type_of(ov, item->loc);
    if (assigned.written.kind != DataTypeKind::kImplicit) {
      return ChildTypeParamBinding{std::move(assigned), ov};
    }
    ReportTypeParamAssignedNoType({pname, child_decl->name}, ov->range.start,
                                  diag);
    return std::nullopt;
  }
  if (TypeParamPortHasDefault(child_decl->param_types.at(i))) {
    return ChildTypeParamBinding{DefaultChildType(from, child_decl, i)};
  }
  diag.Error(item->loc,
             std::format("type parameter '{}' of '{}' has no default type "
                         "and no override at instantiation",
                         pname, child_decl->name),
             Subclause("6.20.1"));
  return std::nullopt;
}

AppliedTypeParams ApplyChildTypeParams(const TypeParamAssignments& from,
                                       const ModuleDecl* child_decl,
                                       TypedefMap& typedefs, DiagEngine& diag) {
  AppliedTypeParams applied;
  std::vector<std::pair<std::string_view, DataType>> resolved_params;
  for (size_t i = 0; i < child_decl->params.size(); ++i) {
    std::string_view pname = child_decl->params[i].first;
    if (child_decl->type_param_names.count(pname) == 0) continue;
    auto binding = ResolveChildTypeParam(from, child_decl, i, diag);
    if (!binding) continue;
    const DataType& in_scope = binding->type.resolved.element;
    if (in_scope.kind == DataTypeKind::kImplicit) continue;
    if (binding->override_expr != nullptr) {
      applied.overrides.push_back(
          {pname, in_scope, binding->override_expr->range.start});
    }
    resolved_params.emplace_back(pname, in_scope);
    applied.written[pname] = std::move(binding->type);
  }
  for (auto& [pname, type] : resolved_params) {
    SavedTypedef s;
    s.name = pname;
    auto it = typedefs.find(pname);
    s.existed = it != typedefs.end();
    if (s.existed) s.prev = it->second;
    applied.saved.push_back(s);
    typedefs[pname] = std::move(type);
  }
  return applied;
}

void ReportChildTypeParamsOutsideRestrictions(
    const ModuleDecl* decl, const AppliedTypeParams& applied,
    const TypeParamRestrictionScope& scope, DiagEngine& diag) {
  const auto& restrictions = decl->type_param_restrictions;
  for (size_t i = 0; i < decl->params.size(); ++i) {
    auto restriction = restrictions.find(decl->params[i].first);
    if (restriction == restrictions.end()) continue;
    ReportTypeOutsideRestriction({restriction->first, restriction->second},
                                 decl->param_types.at(i),
                                 decl->param_port_locs.at(i), scope, diag);
  }
  for (const OverridingType& ov : applied.overrides) {
    auto restriction = restrictions.find(ov.name);
    if (restriction == restrictions.end()) continue;
    ReportTypeOutsideRestriction({ov.name, restriction->second}, ov.type,
                                 ov.loc, scope, diag);
  }
}

void RestoreChildTypeParams(TypedefMap& typedefs,
                            const std::vector<SavedTypedef>& saved) {
  for (const auto& s : saved) {
    if (s.existed)
      typedefs[s.name] = s.prev;
    else
      typedefs.erase(s.name);
  }
}

}  // namespace delta
