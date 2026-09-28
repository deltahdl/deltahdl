#include "elaborator/elaborator_child_type_params.h"

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

// §33.4.3 with Syntax 33-4: a use clause's named_parameter_assignment may name
// a type parameter, its value a data type. The configuration's assignment for
// `pname`, or nullptr.
static const Expr* ConfigTypeParamOverride(const TypeParamAssignments& from,
                                           std::string_view pname) {
  for (const auto& [name, expr] : from.config) {
    if (name == pname) return expr;
  }
  return nullptr;
}

// §23.10.2/§6.20.3: the type the child's type parameter at index `i` takes for
// this instantiation -- the instance parameter value assignment when one names
// a type, otherwise the type the declaration defaulted to. Returns nothing,
// having reported, when the assignment names no type, and when there is neither
// an assignment nor a default (§6.20.1). Reporting an assignment that names no
// type is what keeps it apart from an absent one: falling back to the default
// there would elaborate the child against a type the source did not write, and
// the mismatch would surface as a wrong width rather than as a report.
static std::optional<DataType> ResolveChildTypeParam(
    const TypeParamAssignments& from, const ModuleDecl* child_decl, size_t i,
    const CompilationUnit* unit, DiagEngine& diag) {
  const ModuleItem* item = from.item;
  std::string_view pname = child_decl->params[i].first;
  const Expr* ov = ConfigTypeParamOverride(from, pname);
  if (ov == nullptr && !from.config_reset_all) {
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

// §23.10.2: a parameter value assignment is written in the instantiating
// module, so a type name it gives, a typedef or type parameter of that module,
// stands for the type the name has there and not for a child's declaration of
// the same name. `typedefs` still holds the instantiating module's names, and
// the name is replaced by the type it stands for among them. Published as the
// name, `child #(bus_t)` into a child whose own type parameter is bus_t made
// bus_t stand for itself, and sizing it recursed without end. A name carrying
// packed dimensions written on it, and one scoped to a class or package, keep
// their form; the hop limit keeps a cyclic typedef from looping.
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

// §6.20.3/§23.10: resolve each of the child's type parameters to a concrete
// type and publish it in `typedefs` so the child's dependent declarations
// elaborate against the chosen type. Every type is resolved before any is
// published, so each override reads the instantiating module's names. A type
// parameter whose type ResolveChildTypeParam could not settle publishes
// nothing, so the child's declarations that depend on it are left unresolved
// rather than bound to a type the instantiation did not ask for. Returns the
// prior entries so the caller can restore the shared map after the child is
// elaborated.
std::vector<SavedTypedef> ApplyChildTypeParams(const TypeParamAssignments& from,
                                               const ModuleDecl* child_decl,
                                               TypedefMap& typedefs,
                                               const CompilationUnit* unit,
                                               DiagEngine& diag) {
  std::vector<std::pair<std::string_view, DataType>> resolved_params;
  for (size_t i = 0; i < child_decl->params.size(); ++i) {
    std::string_view pname = child_decl->params[i].first;
    if (child_decl->type_param_names.count(pname) == 0) continue;
    auto resolved = ResolveChildTypeParam(from, child_decl, i, unit, diag);
    if (!resolved) continue;
    resolved_params.emplace_back(pname,
                                 InInstantiatingScope(*resolved, typedefs));
  }
  std::vector<SavedTypedef> saved;
  for (auto& [pname, type] : resolved_params) {
    SavedTypedef s;
    s.name = pname;
    auto it = typedefs.find(pname);
    s.existed = it != typedefs.end();
    if (s.existed) s.prev = it->second;
    saved.push_back(s);
    typedefs[pname] = std::move(type);
  }
  return saved;
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
