#include "elaborator/elaborator_items_params.h"

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <format>
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
#include "elaborator/type_parameter_values.h"
#include "elaborator/unpacked_array_type.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

namespace delta {

static bool IsRealIdentifier(const Expr* e) {
  if (e->scope_prefix.empty()) {
    if (ConstFuncRealLocal(e->text)) return true;
    if (DeclaresLocalName(e->text)) return false;
    if (const RtlirParamDecl* pd = RegisteredParamNamed(e->text))
      return pd->is_real_value;
  }
  return IsRealAggregatePart(e);
}

static bool IsRealOperand(const Expr* e) {
  if (e->kind == ExprKind::kRealLiteral || e->kind == ExprKind::kTimeLiteral)
    return true;
  if (e->kind == ExprKind::kIdentifier) return IsRealIdentifier(e);
  if (e->kind == ExprKind::kCall) {
    const ModuleItem* fn = RegisteredConstFunc(e);
    if (fn != nullptr) return IsConstFuncRealType(fn->return_type);
  }
  if (e->kind == ExprKind::kSelect || e->kind == ExprKind::kMemberAccess)
    return IsRealAggregatePart(e);
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

bool TakesItsTypeFromItsValue(const DataType& type) {
  return type.kind == DataTypeKind::kImplicit && !type.is_signed &&
         type.packed_dim_left == nullptr;
}

bool HoldsRealValue(const DataType& type, const Expr* value) {
  if (TakesItsTypeFromItsValue(type)) return HasRealOperand(value);
  return IsRealType(type.kind);
}

std::optional<int64_t> FoldRealValueAsInteger(const Expr* expr,
                                              const ScopeMap& scope) {
  if (!HasRealOperand(expr)) return std::nullopt;
  auto rval = ConstEvalReal(expr, scope);
  if (!rval || !std::isfinite(*rval)) return std::nullopt;
  return std::llround(*rval);
}

std::optional<int64_t> FoldParamValueRoundingReal(const Expr* value,
                                                  const DataType& type,
                                                  const ScopeMap& scope) {
  if (auto rounded = FoldRealValueAsInteger(value, scope)) return rounded;
  return FoldDeclaredParamValue(value, type, scope);
}

void ResolveConstantValue(RtlirParamDecl& pd, const Expr* init,
                          const DataType& type, const ScopeMap& scope) {
  if (TryFoldRealParamValue(pd, init, type, scope)) return;
  std::optional<int64_t> val;
  if (ParamExpectsIntegerValue(pd, type)) {
    val = FoldRealValueAsInteger(init, scope);
  }
  if (!val) val = FoldParamValue(pd, init, scope);
  if (!val) return;
  pd.resolved_value = *val;
  pd.is_resolved = true;
  RecordResolvedHighWords(pd, init, scope);
}

namespace {

void CheckTypeParamNotSetToValue(const ModuleItem* item, DiagEngine& diag) {
  if (item->data_type.kind == DataTypeKind::kVoid &&
      item->typedef_type.kind == DataTypeKind::kImplicit) {
    ReportTypeParamSetToNoType(item->name, item->loc, diag);
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
  if (is_type) return;
  ResolveConstantValue(pd, item->init_expr, item->data_type, scope);
  if (pd.is_real_value) return;
  RecordStringParamValue(pd, item->init_expr, &item->data_type, arena);
}

struct AssignedTypeParam {
  AssignedType type;
  SourceLoc loc;
};

std::optional<AssignedTypeParam> AssignedTypeParamType(
    const ModuleItem* item, RtlirParamDecl& pd, const RtlirModule* mod,
    const AssignedType& default_type, DiagEngine& diag) {
  const InstanceParamAssignments* assigns =
      pd.is_localparam || !pd.gen_block_prefix.empty() ? nullptr
                                                       : BodyParamAssignments();
  const Elaborator::ParamOverride* ovr =
      assigns == nullptr ? nullptr
                         : FindParamOverride(assigns->params, item->name);
  if (ovr == nullptr || ovr->value_expr == nullptr) {
    return AssignedTypeParam{default_type, item->loc};
  }
  const SourceLoc kLoc = ovr->value_expr->range.start;
  if (ovr->assigned_type->written.kind == DataTypeKind::kImplicit) {
    ReportTypeParamAssignedNoType({item->name, mod->name}, kLoc, diag);
    return std::nullopt;
  }
  pd.from_override = true;
  return AssignedTypeParam{*ovr->assigned_type, kLoc};
}

void ReportAssignedTypeOutsideRestriction(
    const ModuleItem* item, const AssignedTypeParam& assigned,
    const TypeParamRestrictionScope& scope, DiagEngine& diag) {
  const RestrictedTypeParam kParam{item->name, item->forward_type_kind};
  ReportTypeOutsideRestriction(kParam, item->typedef_type, item->loc, scope,
                               diag);
  ReportTypeOutsideRestriction(kParam, assigned.type.resolved.element,
                               assigned.loc, scope, diag);
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

void Elaborator::ResolveBodyTypeParam(const ModuleItem* item,
                                      const AssignedType& default_type,
                                      RtlirParamDecl& pd, RtlirModule* mod) {
  ReportTypeParamPrefixNotAClass(item->typedef_type.scope_name, item->loc,
                                 {mod->params, typedefs_, class_names_, unit_},
                                 diag_);
  auto assigned = AssignedTypeParamType(item, pd, mod, default_type, diag_);
  if (!assigned) return;
  ReportAssignedTypeOutsideRestriction(item, *assigned,
                                       {typedefs_, unit_, class_names_}, diag_);
  RecordTypedef(typedefs_, item->name, assigned->type.resolved.element);
  BindTypeParamDims(item->name, assigned->type.resolved.dims);
  pd.resolved_type = arena_.Create<DataType>(assigned->type.written);
}

AssignedType Elaborator::BodyTypeParamDefault(ModuleItem* item,
                                              RtlirModule* mod) {
  if (item->data_type.kind != DataTypeKind::kVoid) return {};
  if (item->init_expr != nullptr &&
      item->init_expr->kind == ExprKind::kTypeRef) {
    AssignedType referenced = TypeAssignedIn(mod, item->init_expr, item->loc);
    item->typedef_type = referenced.written;
    return referenced;
  }
  return {item->typedef_type,
          WithTypedefDims(item->typedef_type, {},
                          {typedefs_, td_array_dims_, class_names_})};
}

void Elaborator::ElaborateParamDecl(ModuleItem* item, RtlirModule* mod) {
  ResolveTypeRef(item->data_type, item->loc, mod);
  const AssignedType kDefaultType = BodyTypeParamDefault(item, mod);
  const bool kIsType = kDefaultType.written.kind != DataTypeKind::kImplicit;

  CheckTypeParamNotSetToValue(item, diag_);

  RtlirParamDecl pd;
  pd.name = item->name;
  pd.loc = item->loc;
  pd.gen_block_prefix = InternedGenPrefix();
  pd.is_type_param = kIsType;

  pd.is_localparam = item->is_localparam || mod->has_param_port_list;
  pd.default_value = item->init_expr;
  if (!item->unpacked_dims.empty()) pd.unpacked_dims = &item->unpacked_dims;
  if (kIsType) {
    ResolveBodyTypeParam(item, kDefaultType, pd, mod);
    DeclareTypeParamEnums(item->typedef_type, pd, pd.from_override, mod);
  } else {
    EmitDeclarationEnumMembers(item, true, mod);
  }
  const ScopeMap kScope = BuildParamScope(mod);
  FoldParamUnpackedBounds(pd, kScope);
  if (!kIsType) {
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
    ResolveParamConstValue(pd, item, kIsType, kScope, arena_);
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
