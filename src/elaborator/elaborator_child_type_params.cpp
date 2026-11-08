#include "elaborator/elaborator_child_type_params.h"

#include <algorithm>
#include <cstddef>
#include <format>
#include <optional>
#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator_items_params.h"
#include "elaborator/type_eval.h"
#include "parser/ast_design.h"
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

static std::optional<DataType> ResolveChildTypeParam(
    const TypeParamAssignments& from, const ModuleDecl* child_decl, size_t i,
    const CompilationUnit* unit, DiagEngine& diag) {
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
    DataType resolved = TypeParamOverrideToDataType(ov, unit, diag, item->loc);
    if (resolved.kind != DataTypeKind::kImplicit) return resolved;
    diag.Error(item->loc,
               std::format("parameter value assignment for type parameter '{}' "
                           "of '{}' does not name a type",
                           pname, child_decl->name),
               Subclause("23.10.2"));
    return std::nullopt;
  }
  if (i < child_decl->param_types.size() &&
      child_decl->param_types[i].kind != DataTypeKind::kImplicit) {
    return child_decl->param_types[i];
  }
  diag.Error(item->loc,
             std::format("type parameter '{}' of '{}' has no default type "
                         "and no override at instantiation",
                         pname, child_decl->name),
             Subclause("6.20.1"));
  return std::nullopt;
}

static DataType InInstantiatingScope(DataType dt, const TypedefMap& typedefs) {
  for (int hops = 0; hops < 8 && dt.kind == DataTypeKind::kNamed &&
                     dt.scope_name.empty() && dt.packed_dim_left == nullptr;
       ++hops) {
    auto it = typedefs.find(dt.type_name);
    if (it == typedefs.end()) break;
    dt = it->second;
  }
  return dt;
}

AppliedTypeParams ApplyChildTypeParams(const TypeParamAssignments& from,
                                       const ModuleDecl* child_decl,
                                       TypedefMap& typedefs,
                                       const CompilationUnit* unit,
                                       DiagEngine& diag) {
  AppliedTypeParams applied;
  std::vector<std::pair<std::string_view, DataType>> resolved_params;
  for (size_t i = 0; i < child_decl->params.size(); ++i) {
    std::string_view pname = child_decl->params[i].first;
    if (child_decl->type_param_names.count(pname) == 0) continue;
    auto resolved = ResolveChildTypeParam(from, child_decl, i, unit, diag);
    if (!resolved) continue;
    resolved_params.emplace_back(pname,
                                 InInstantiatingScope(*resolved, typedefs));
    applied.written[pname] = *resolved;
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

bool AllTypeParamsHaveDefaults(const ModuleDecl* decl) {
  for (size_t i = 0; i < decl->params.size(); ++i) {
    if (decl->type_param_names.count(decl->params[i].first) == 0) continue;
    if (i >= decl->param_types.size() ||
        decl->param_types[i].kind == DataTypeKind::kImplicit) {
      return false;
    }
  }
  return true;
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
