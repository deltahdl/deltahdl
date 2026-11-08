#include "elaborator/elaborator_items_params.h"

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <format>
#include <functional>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/net_data_type.h"
#include "elaborator/param_value_assignability.h"
#include "elaborator/rtlir.h"
#include "elaborator/simple_bit_vector.h"
#include "elaborator/type_eval.h"
#include "elaborator/type_param_restriction.h"
#include "elaborator/type_param_scope_prefix.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

namespace delta {

static bool IsRealOperand(const Expr* e) {
  if (e->kind == ExprKind::kRealLiteral || e->kind == ExprKind::kTimeLiteral)
    return true;
  if (e->kind == ExprKind::kIdentifier) {
    if (ConstFuncRealLocal(e->text)) return true;
    const RtlirParamDecl* pd = RegisteredParamNamed(e->text);
    return pd != nullptr && pd->is_real_value;
  }
  if (e->kind == ExprKind::kCall) {
    const ModuleItem* fn = RegisteredConstFunc(e);
    if (fn != nullptr) return IsConstFuncRealType(fn->return_type);
  }
  if (e->kind != ExprKind::kSystemCall && e->kind != ExprKind::kCall)
    return false;
  return e->callee == "$itor" || e->callee == "$bitstoreal" ||
         e->callee == "$bitstoshortreal";
}

bool HasRealOperand(const Expr* e) {
  if (e == nullptr) return false;
  if (IsRealOperand(e)) return true;
  const Expr* const kChildren[] = {e->lhs, e->rhs, e->condition, e->true_expr,
                                   e->false_expr};
  for (const Expr* c : kChildren) {
    if (HasRealOperand(c)) return true;
  }
  for (const Expr* a : e->args) {
    if (HasRealOperand(a)) return true;
  }
  return false;
}

std::optional<int64_t> FoldRealValueAsInteger(const Expr* expr,
                                              const ScopeMap& scope) {
  if (!HasRealOperand(expr)) return std::nullopt;
  auto rval = ConstEvalReal(expr, scope);
  if (!rval || !std::isfinite(*rval)) return std::nullopt;
  return std::llround(*rval);
}

namespace {

void CheckTypeParamNotSetToValue(const ModuleItem* item, DiagEngine& diag) {
  if (item->data_type.kind == DataTypeKind::kVoid &&
      item->typedef_type.kind == DataTypeKind::kImplicit &&
      item->init_expr != nullptr &&
      item->init_expr->kind != ExprKind::kTypeRef) {
    diag.Error(item->loc,
               std::format("type parameter '{}' can only be set to a data "
                           "type, not a value expression",
                           item->name),
               Subclause("6.20.3"));
  }
}

void PopulateValueParamInfo(
    RtlirParamDecl& pd, const ModuleItem* item,
    std::unordered_set<std::string_view>& real_param_names,
    const TypedefMap& typedefs, const ScopeMap& scope) {
  pd.decl_type = &item->data_type;
  PopulateParamTypeInfo(pd, item->data_type, typedefs, scope);
  if (item->unpacked_dims.empty() && pd.decl_is_real) {
    real_param_names.insert(item->name);
  }
}

void ResolveParamConstValue(RtlirParamDecl& pd, const ModuleItem* item,
                            bool is_type, const ScopeMap& scope, Arena& arena) {
  if (!is_type &&
      TryFoldRealParamValue(pd, item->init_expr, item->data_type, scope))
    return;
  std::optional<int64_t> val;
  if (!is_type && ParamExpectsIntegerValue(pd, item->data_type))
    val = FoldRealValueAsInteger(item->init_expr, scope);
  if (!val) val = FoldParamValue(pd, item->init_expr, scope);
  if (val) {
    pd.resolved_value = *val;
    pd.is_resolved = true;
    RecordResolvedHighWords(pd, item->init_expr, scope);
  }
  if (!is_type)
    RecordStringParamValue(pd, item->init_expr, &item->data_type, arena);
}

bool ResolveTypeOperatorDefault(
    ModuleItem* item, const CompilationUnit* unit,
    const std::function<void(DataType&)>& resolve_expr_type) {
  if (item->data_type.kind != DataTypeKind::kVoid ||
      item->typedef_type.kind != DataTypeKind::kImplicit ||
      item->init_expr == nullptr || item->init_expr->kind != ExprKind::kTypeRef)
    return false;
  const Expr* ref = item->init_expr;
  if (ref->text.empty()) {
    if (ref->lhs == nullptr) return false;
    DataType dt;
    dt.type_ref_expr = ref->lhs;
    resolve_expr_type(dt);
    if (dt.type_ref_expr == nullptr) item->typedef_type = dt;
  } else if (ref->scope_prefix.empty()) {
    item->typedef_type = ref->type_value != nullptr
                             ? *ref->type_value
                             : TypeNameToDataType(ref->text);
  } else if (const DataType* scoped = FindClassScopedTypedefType(
                 ref->scope_prefix, ref->text, unit)) {
    item->typedef_type = *scoped;
  }
  return item->typedef_type.kind != DataTypeKind::kImplicit;
}

struct AssignedTypeParam {
  DataType type;
  SourceLoc loc;
};

std::optional<AssignedTypeParam> AssignedTypeParamType(
    const ModuleItem* item, RtlirParamDecl& pd, const RtlirModule* mod,
    const CompilationUnit* unit, DiagEngine& diag) {
  const InstanceParamAssignments* assigns =
      pd.is_localparam || !pd.gen_block_prefix.empty() ? nullptr
                                                       : BodyParamAssignments();
  const Elaborator::ParamOverride* ovr =
      assigns == nullptr ? nullptr
                         : FindParamOverride(assigns->params, item->name);
  if (ovr == nullptr || ovr->value_expr == nullptr) {
    return AssignedTypeParam{item->typedef_type, item->loc};
  }
  const SourceLoc kLoc = ovr->value_expr->range.start;
  DataType resolved =
      TypeParamOverrideToDataType(ovr->value_expr, unit, diag, kLoc);
  if (resolved.kind == DataTypeKind::kImplicit) {
    diag.Error(kLoc,
               std::format("parameter value assignment for type parameter '{}' "
                           "of '{}' does not name a type",
                           item->name, mod->name),
               Subclause("23.10.2"));
    return std::nullopt;
  }
  pd.from_override = true;
  return AssignedTypeParam{resolved, kLoc};
}

void ReportAssignedTypeOutsideRestriction(
    const ModuleItem* item, const AssignedTypeParam& assigned,
    const TypeParamRestrictionScope& scope, DiagEngine& diag) {
  const RestrictedTypeParam kParam{item->name, item->forward_type_kind};
  ReportTypeOutsideRestriction(kParam, item->typedef_type, item->loc, scope,
                               diag);
  ReportTypeOutsideRestriction(kParam, assigned.type, assigned.loc, scope,
                               diag);
}

void ApplyBodyParamAssignment(RtlirParamDecl& pd, const ModuleItem* item,
                              Arena& arena, const ParamValueScope& target,
                              DiagEngine& diag) {
  if (pd.is_localparam || !pd.gen_block_prefix.empty()) return;
  const InstanceParamAssignments* assigns = BodyParamAssignments();
  if (assigns == nullptr) return;
  ApplyParamOverride(pd, *assigns, item->name, target.tables.typedefs, arena);
  CheckDollarOverride(
      *assigns,
      {item->name, nullptr, &item->data_type, !item->unpacked_dims.empty()},
      target.tables, diag);
  ReportInstanceOverrideType(pd, *assigns, target, diag);
}

}  // namespace

static void RecordUntypedRealParam(
    const RtlirParamDecl& pd, const ModuleItem* item,
    std::unordered_set<std::string_view>& real_param_names) {
  if (pd.is_real_value && item->unpacked_dims.empty())
    real_param_names.insert(item->name);
}

void FoldParamUnpackedBounds(RtlirParamDecl& pd, const ScopeMap& scope) {
  if (pd.unpacked_dims == nullptr) return;
  std::vector<RtlirUnpackedDim> bounds;
  for (const Expr* dim : *pd.unpacked_dims) {
    auto folded = FoldUnpackedDimBounds(dim, scope);
    if (!folded) return;
    bounds.push_back(*folded);
  }
  pd.unpacked_bounds = std::move(bounds);
}

void RecordTypeParamActual(RtlirParamDecl& pd,
                           const std::vector<RtlirParamDecl>& earlier,
                           const TypedefMap& typedefs, Arena& arena) {
  const DataType* dt = pd.decl_type;
  if (dt == nullptr || dt->kind != DataTypeKind::kNamed ||
      !dt->scope_name.empty())
    return;
  auto names_it = [&](const RtlirParamDecl& p) {
    return p.is_type_param && p.name == dt->type_name;
  };
  auto tp = std::find_if(earlier.rbegin(), earlier.rend(), names_it);
  if (tp == earlier.rend()) return;
  auto bound = typedefs.find(dt->type_name);
  pd.type_param_actual = bound != typedefs.end()
                             ? arena.Create<DataType>(bound->second)
                             : tp->resolved_type;
}

void Elaborator::ElaborateParamDecl(ModuleItem* item, RtlirModule* mod) {
  ResolveTypeRef(item->data_type, item->loc, mod);
  bool is_type = item->data_type.kind == DataTypeKind::kVoid &&
                 item->typedef_type.kind != DataTypeKind::kImplicit;
  if (!is_type) {
    is_type = ResolveTypeOperatorDefault(
        item, unit_, [&](DataType& dt) { ResolveTypeRef(dt, item->loc, mod); });
  }

  CheckTypeParamNotSetToValue(item, diag_);

  RtlirParamDecl pd;
  pd.name = item->name;
  pd.loc = item->loc;
  pd.gen_block_prefix = InternedGenPrefix();
  pd.is_type_param = is_type;

  pd.is_localparam = item->is_localparam || mod->has_param_port_list;
  pd.default_value = item->init_expr;
  if (!item->unpacked_dims.empty()) pd.unpacked_dims = &item->unpacked_dims;
  if (is_type) {
    ReportTypeParamPrefixNotAClass(item->typedef_type.scope_name, item->loc,
                                   {mod->params, typedefs_, class_names_},
                                   diag_);
    if (auto assigned = AssignedTypeParamType(item, pd, mod, unit_, diag_)) {
      ReportAssignedTypeOutsideRestriction(
          item, *assigned, {typedefs_, unit_, class_names_}, diag_);
      typedefs_[item->name] = assigned->type;
      pd.resolved_type = arena_.Create<DataType>(assigned->type);
    }
  }
  const ScopeMap kScope = BuildParamScope(mod);
  FoldParamUnpackedBounds(pd, kScope);
  if (!is_type) {
    PopulateValueParamInfo(pd, item, real_param_names_, typedefs_, kScope);
    RecordTypeParamActual(pd, mod->params, typedefs_, arena_);
    RecordParamDeclRange(pd, item->data_type, kScope);
    const TypeShapeTables kTables{typedefs_, td_array_dims_, class_names_};
    ApplyBodyParamAssignment(pd, item, arena_, {kTables, kScope, unit_}, diag_);
  }

  const bool kFoldsDefault = item->init_expr != nullptr && !pd.from_override;
  if (kFoldsDefault && item->init_expr->kind == ExprKind::kIdentifier &&
      (item->init_expr->text == "$" ||
       RefersToUnboundedParam(mod, item->init_expr->text))) {
    pd.is_unbounded = true;
    ValidateUnboundedParamType(
        {item->name, &item->data_type, !item->unpacked_dims.empty(), item->loc},
        {typedefs_, td_array_dims_, class_names_}, diag_);
  } else if (kFoldsDefault) {
    if (ContainsDollarSubexpr(item->init_expr)) {
      diag_.Error(item->loc,
                  std::format("'$' may only be assigned to parameter '{}' as a "
                              "complete, self-contained expression",
                              item->name),
                  Subclause("6.20.7"));
    }
    ValidateTypenameAsElabConstant(item->init_expr);
    ResolveParamConstValue(pd, item, is_type, kScope, arena_);
    RecordUntypedRealParam(pd, item, real_param_names_);
  }
  mod->params.push_back(pd);

  const_names_.insert(item->name);
}

std::unordered_map<std::string_view, const ClassDecl*> BuildParamClassRegistry(
    const CompilationUnit* unit) {
  std::unordered_map<std::string_view, const ClassDecl*> registry;
  for (const auto* cls : unit->classes) {
    if (!cls->params.empty()) registry.emplace(cls->name, cls);
  }
  return registry;
}

}  // namespace delta
