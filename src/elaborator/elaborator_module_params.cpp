#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <format>
#include <functional>
#include <optional>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/covergroup_variables.h"
#include "elaborator/dollar_contexts.h"
#include "elaborator/dollar_parameter_values.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_child_type_params.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_params.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/net_data_type.h"
#include "elaborator/param_value_assignability.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/simple_bit_vector.h"
#include "elaborator/type_eval.h"
#include "elaborator/type_parameter_values.h"
#include "elaborator/unpacked_array_type.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "parser/ast_type.h"

namespace delta {

const Elaborator::ParamOverride* FindParamOverride(
    const Elaborator::ParamList& params, std::string_view name) {
  for (const auto& ovr : params) {
    if (ovr.name == name) {
      return &ovr;
    }
  }
  return nullptr;
}

static bool ParamTypeResolvesToClass(
    const DataType& dtype, const TypedefMap& typedefs,
    const std::unordered_set<std::string_view>& class_names) {
  const DataType* cur = &dtype;
  for (int depth = 0; depth < 32 && cur->kind == DataTypeKind::kNamed;
       ++depth) {
    if (class_names.count(cur->type_name) > 0) return true;
    auto it = typedefs.find(cur->type_name);
    if (it == typedefs.end()) break;
    cur = &it->second;
  }
  return false;
}

struct TypeParamValueCtx {
  const TypedefMap& typedefs;
  const std::unordered_set<std::string_view>& class_names;
  DiagEngine& diag;
};

static void CheckTypeParamValueAssignable(const ModuleDecl* decl, size_t i,
                                          const Expr* pval,
                                          const ScopeMap& scope,
                                          const TypeParamValueCtx& ctx) {
  if (i >= decl->param_types.size()) return;
  const DataType& dt = decl->param_types[i];
  if (dt.kind != DataTypeKind::kNamed) return;
  if (decl->type_param_names.count(dt.type_name) == 0) return;
  if (!pval || !ConstEvalInt(pval, scope)) return;
  if (!ParamTypeResolvesToClass(dt, ctx.typedefs, ctx.class_names)) return;
  ctx.diag.Error(pval->range.start,
                 std::format("cannot assign an integral value to parameter "
                             "whose type parameter '{}' resolved to a class "
                             "type",
                             dt.type_name),
                 Subclause("23.10.3"));
}

bool HasParamPortWithoutDefault(const ModuleDecl* decl) {
  for (size_t i = 0; i < decl->params.size(); ++i) {
    const auto& [name, expr] = decl->params[i];
    if (decl->localparam_port_names.count(name)) continue;
    if (decl->type_param_names.count(name)
            ? !TypeParamPortHasDefault(decl->param_types.at(i))
            : expr == nullptr) {
      return true;
    }
  }
  return false;
}

void ReportParamsMissingValue(const RtlirModule& mod,
                              std::unordered_set<const RtlirModule*>& judged,
                              DiagEngine& diag) {
  if (!judged.insert(&mod).second) return;
  for (const auto& pd : mod.params) {
    if (pd.is_localparam || pd.is_type_param) continue;
    if (pd.default_value != nullptr || pd.from_override) continue;
    diag.Error(mod.loc,
               std::format("parameter '{}' of '{}' has no default value and "
                           "no override at instantiation",
                           pd.name, mod.name),
               Subclause("6.20.1"));
  }
  for (const auto& child : mod.children) {
    if (child.resolved != nullptr) {
      ReportParamsMissingValue(*child.resolved, judged, diag);
    }
  }
}

std::unordered_set<std::string_view> DeclaredSpecparamNames(
    const ModuleDecl* decl) {
  std::unordered_set<std::string_view> names;
  if (decl == nullptr) return names;
  for (const ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kSpecparam) names.insert(item->name);
    if (item->kind != ModuleItemKind::kSpecifyBlock) continue;
    for (const SpecifyItem* sp : item->specify_items) {
      if (sp->kind != SpecifyItemKind::kSpecparam || sp->is_pathpulse) continue;
      if (sp->param_name.starts_with("PATHPULSE$")) continue;
      names.insert(sp->param_name);
    }
  }
  return names;
}

void PopulateParamTypeInfo(RtlirParamDecl& pd, const DataType& dtype) {
  pd.has_decl_range = dtype.packed_dim_left != nullptr;
  pd.decl_is_real = IsRealType(dtype.kind);
  pd.decl_is_shortreal = dtype.kind == DataTypeKind::kShortreal;
  pd.has_decl_type = dtype.kind != DataTypeKind::kImplicit || dtype.is_signed;
  pd.decl_is_signed = dtype.is_signed;
  pd.decl_type_implicit = dtype.kind == DataTypeKind::kImplicit;
  if (pd.has_decl_range || pd.has_decl_type) {
    pd.decl_width = EvalTypeWidth(dtype);
  }
}

void PopulateParamTypeInfo(RtlirParamDecl& pd, const DataType& dtype,
                           const TypedefMap& typedefs, const ScopeMap& scope) {
  pd.has_decl_range = dtype.packed_dim_left != nullptr;
  DataTypeKind kind = ResolvedTypeKind(dtype, typedefs);
  pd.decl_is_real = IsRealType(kind);
  pd.decl_is_shortreal = kind == DataTypeKind::kShortreal;
  pd.has_decl_type = dtype.kind != DataTypeKind::kImplicit || dtype.is_signed;
  pd.decl_is_signed = dtype.is_signed;
  pd.decl_type_implicit = dtype.kind == DataTypeKind::kImplicit;
  if (pd.has_decl_range || pd.has_decl_type) {
    pd.decl_width = EvalTypeWidth(dtype, typedefs, scope);
  }
}

void RecordParamDeclRange(RtlirParamDecl& pd, const DataType& dtype,
                          const ScopeMap& scope) {
  if (!dtype.packed_dim_left || !dtype.packed_dim_right) return;
  auto left = ConstEvalInt(dtype.packed_dim_left, scope);
  auto right = ConstEvalInt(dtype.packed_dim_right, scope);
  if (!left || !right) return;
  pd.decl_range_left = *left;
  pd.decl_range_right = *right;
  pd.has_decl_range_bounds = true;
}

bool ParamExpectsIntegerValue(const RtlirParamDecl& pd, const DataType& dtype) {
  return pd.has_decl_range ||
         (pd.has_decl_type && !IsRealType(dtype.kind) && !pd.decl_is_real);
}

static bool TakesRealFromValue(const RtlirParamDecl& pd, const Expr* init,
                               const DataType& dtype) {
  return dtype.kind == DataTypeKind::kImplicit && !pd.has_decl_range &&
         !pd.has_decl_type && HasRealOperand(init);
}

static double HeldAsDeclaredReal(const RtlirParamDecl& pd, double value) {
  return pd.decl_is_shortreal || pd.value_is_shortreal
             ? static_cast<double>(static_cast<float>(value))
             : value;
}

bool TryFoldRealParamValue(RtlirParamDecl& pd, const Expr* init,
                           const DataType& dtype, const ScopeMap& scope) {
  if (!IsRealType(dtype.kind) && !pd.decl_is_real &&
      !TakesRealFromValue(pd, init, dtype))
    return false;
  auto rval = ConstEvalReal(init, scope);
  if (!rval) return false;
  pd.value_is_shortreal =
      TakesRealFromValue(pd, init, dtype) && IsShortrealValue(init);
  pd.resolved_real = HeldAsDeclaredReal(pd, *rval);
  pd.is_real_value = true;
  pd.is_resolved = true;
  return true;
}

bool RecordStringParamChars(RtlirParamDecl& pd, const Expr* init,
                            Arena& arena) {
  auto chars = ConstEvalString(init);
  if (!chars) return false;
  pd.resolved_string = {arena.AllocString(chars->c_str(), chars->size()),
                        chars->size()};
  pd.is_string_value = true;
  return true;
}

void RecordStringParamValue(RtlirParamDecl& pd, const Expr* init,
                            const DataType* dtype, Arena& arena) {
  if (!dtype || dtype->kind != DataTypeKind::kString) return;
  RecordStringParamChars(pd, init, arena);
}

std::optional<double> RealOverrideValue(const Expr* expr,
                                        const ScopeMap& scope) {
  if (expr == nullptr || !HasRealOperand(expr)) return std::nullopt;
  return ConstEvalReal(expr, scope);
}

int64_t RoundRealToInteger(double value) { return std::llround(value); }

void ApplyOverrideRealness(RtlirParamDecl& pd, std::optional<double> real) {
  bool untyped = !pd.has_decl_range && !pd.has_decl_type;
  if (real && (pd.decl_is_real || untyped)) {
    pd.resolved_real = HeldAsDeclaredReal(pd, *real);
    pd.is_real_value = true;
  } else if (pd.decl_is_real) {
    pd.resolved_real =
        HeldAsDeclaredReal(pd, static_cast<double>(pd.resolved_value));
    pd.is_real_value = true;
  } else {
    pd.is_real_value = false;
  }
}

int64_t ConvertOverrideValue(int64_t value, const RtlirParamDecl& pd) {
  bool has_fixed_width =
      pd.has_decl_range || (pd.has_decl_type && !pd.decl_type_implicit);
  if (!has_fixed_width) return value;
  uint32_t w = pd.decl_width;
  if (w == 0 || w >= 64) return value;
  uint64_t mask = (uint64_t{1} << w) - 1;
  uint64_t masked = static_cast<uint64_t>(value) & mask;
  if (pd.decl_is_signed) {
    uint64_t sign_bit = uint64_t{1} << (w - 1);
    if (masked & sign_bit) masked |= ~mask;
  }
  return static_cast<int64_t>(masked);
}

static void FoldParamConstantValue(RtlirParamDecl& pd, const Expr* pval,
                                   const ScopeMap& scope, bool has_param_type,
                                   const DataType* param_type) {
  if (has_param_type && param_type != nullptr &&
      TryFoldRealParamValue(pd, pval, *param_type, scope))
    return;
  std::optional<int64_t> val;
  if (!pd.is_type_param && has_param_type &&
      ParamExpectsIntegerValue(pd, *param_type))
    val = FoldRealValueAsInteger(pval, scope);
  if (!val) val = FoldParamValue(pd, pval, scope);
  if (val) {
    pd.resolved_value = *val;
    pd.is_resolved = true;
    RecordResolvedHighWords(pd, pval, scope);
  }
}

struct ParamValueExpr {
  const Expr* pval;
  std::string_view pname;
  bool refers_to_unbounded;
  bool contains_dollar;
  bool has_param_type;
  const DataType* param_type;
  bool has_unpacked_dims;
  const TypeShapeTables& tables;
};

static bool TryResolveUnboundedParamValue(RtlirParamDecl& pd,
                                          const ParamValueExpr& val,
                                          DiagEngine& diag) {
  if (val.pval->kind != ExprKind::kIdentifier ||
      (val.pval->text != "$" && !val.refers_to_unbounded)) {
    return false;
  }
  pd.is_unbounded = true;
  ValidateUnboundedParamType(
      {val.pname, val.param_type, val.has_unpacked_dims, val.pval->range.start},
      val.tables, diag);
  return true;
}

static void ResolveUnresolvedParamValue(RtlirParamDecl& pd,
                                        const ParamValueExpr& val,
                                        const ScopeMap& scope,
                                        DiagEngine& diag) {
  if (TryResolveUnboundedParamValue(pd, val, diag)) {
    return;
  }
  if (val.contains_dollar) {
    diag.Error(val.pval->range.start,
               std::format("'$' may only be assigned to parameter '{}' "
                           "as a complete, self-contained expression",
                           val.pname),
               Subclause("6.20.7"));
  }
  FoldParamConstantValue(pd, val.pval, scope, val.has_param_type,
                         val.param_type);
}

static std::optional<int64_t> ContextOverrideValue(
    const RtlirParamDecl& pd, const Elaborator::ParamOverride& ovr,
    const ScopeMap& scope) {
  if (DeclaredFoldContext(pd).width == 0) return std::nullopt;
  auto self = ConstEvalInt(ovr.value_expr, scope);
  if (!self || *self != ovr.value) return std::nullopt;
  return FoldParamValue(pd, ovr.value_expr, scope);
}

static bool HoldsUnpackedAggregate(const RtlirParamDecl& pd,
                                   const TypedefMap& typedefs) {
  if (pd.unpacked_dims != nullptr) return true;
  const DataType* type =
      pd.type_param_actual != nullptr ? pd.type_param_actual : pd.decl_type;
  if (type == nullptr) return false;
  std::vector<std::string_view> names;
  const DataType* resolved = FollowTypedefs(*type, typedefs, names);
  return resolved != nullptr && IsUnpackedAggregateType(*resolved);
}

bool TakesValueWhole(const RtlirParamDecl& pd, const Expr* value,
                     const TypedefMap& typedefs) {
  return UntypedPattern(value)->kind == ExprKind::kAssignmentPattern ||
         HoldsUnpackedAggregate(pd, typedefs);
}

bool ApplyParamOverride(RtlirParamDecl& pd,
                        const InstanceParamAssignments& assigns,
                        std::string_view pname, const TypedefMap& typedefs,
                        Arena& arena) {
  const auto* ovr = FindParamOverride(assigns.params, pname);
  if (!ovr) return false;
  if (ovr->unfolded && !TakesValueWhole(pd, ovr->value_expr, typedefs))
    return false;
  if (ContainsDollar(ovr->value_expr)) {
    pd.from_override = true;
    pd.is_unbounded = IsLoneDollar(ovr->value_expr);
    return true;
  }
  pd.resolved_value = ConvertOverrideValue(ovr->value, pd);
  pd.is_resolved = true;
  pd.from_override = true;
  pd.value_is_shortreal = ovr->real && !pd.has_decl_range &&
                          !pd.has_decl_type &&
                          IsShortrealValue(ovr->value_expr);
  ApplyOverrideRealness(pd, ovr->real);
  if (ovr->real) return true;
  if (ovr->value_expr != pd.default_value) pd.override_expr = ovr->value_expr;
  if (pd.override_expr != nullptr) {
    if (auto in_context = ContextOverrideValue(pd, *ovr, assigns.scope))
      pd.resolved_value = ConvertOverrideValue(*in_context, pd);
    pd.override_scope = assigns.scope;
    pd.override_module = assigns.module;
    RecordResolvedHighWords(pd, pd.override_expr, assigns.scope);
  }
  RecordStringParamValue(pd, ovr->value_expr, pd.decl_type, arena);
  return true;
}

void ReportInstanceOverrideType(const RtlirParamDecl& pd,
                                const InstanceParamAssignments& assigns,
                                const ParamValueScope& target,
                                DiagEngine& diag) {
  const auto* ovr = FindParamOverride(assigns.params, pd.name);
  if (ovr == nullptr) return;
  ReportOverrideNotAssignable(
      pd, target,
      {ovr->value_expr, assigns.module, assigns.scope, assigns.prefix}, diag);
}

void CheckDollarOverride(const InstanceParamAssignments& assigns,
                         const DollarParamValue& param,
                         const TypeShapeTables& tables, DiagEngine& diag) {
  const auto* ovr = FindParamOverride(assigns.params, param.name);
  if (ovr == nullptr) return;
  DollarParamValue assigned = param;
  assigned.value = ovr->value_expr;
  CheckDollarParamValue(assigned, tables, diag);
}

struct ParamPortCtx {
  const TypedefMap& typedefs;
  const ScopeMap& scope;
  std::unordered_set<std::string_view>& real_param_names;
  const AssignedTypes& written_types;
  Arena& arena;
};

static const DataType* PortTypeParamType(const ModuleDecl* decl, size_t i,
                                         const ParamPortCtx& ctx) {
  auto written = ctx.written_types.find(decl->params[i].first);
  if (written != ctx.written_types.end()) {
    return ctx.arena.Create<DataType>(written->second.written);
  }
  if (i < decl->param_types.size() &&
      decl->param_types[i].kind != DataTypeKind::kImplicit) {
    return ctx.arena.Create<DataType>(decl->param_types[i]);
  }
  return nullptr;
}

static RtlirParamDecl BuildParamDeclShell(const ModuleDecl* decl, size_t i,
                                          const ParamPortCtx& ctx,
                                          bool has_param_type) {
  const auto& [pname, pval] = decl->params[i];
  RtlirParamDecl pd;
  pd.name = pname;
  pd.loc = decl->param_port_locs[i];
  pd.default_value = pval;
  pd.is_resolved = false;
  pd.is_type_param = decl->type_param_names.count(pname) > 0;
  if (pd.is_type_param) pd.resolved_type = PortTypeParamType(decl, i, ctx);
  pd.is_localparam = decl->localparam_port_names.count(pname) > 0;
  auto dims = decl->param_port_unpacked_dims.find(pname);
  if (dims != decl->param_port_unpacked_dims.end()) {
    pd.unpacked_dims = &dims->second;
    FoldParamUnpackedBounds(pd, ctx.scope);
  }
  if (has_param_type) {
    pd.decl_type = &decl->param_types[i];
    PopulateParamTypeInfo(pd, decl->param_types[i], ctx.typedefs, ctx.scope);
    RecordParamDeclRange(pd, decl->param_types[i], ctx.scope);
    if (pd.decl_is_real) ctx.real_param_names.insert(pname);
  }
  return pd;
}

void Elaborator::ResolvePackedStructParam(RtlirParamDecl& pd,
                                          const DataType* type,
                                          const Expr* default_value,
                                          const ScopeMap& scope) {
  if (type == nullptr) return;
  const Expr* value =
      pd.override_expr != nullptr ? pd.override_expr : default_value;
  const ScopeMap& value_scope =
      pd.override_expr != nullptr ? pd.override_scope : scope;
  if (value == nullptr) return;
  auto folded = FoldPackedStructPattern(value, *type, typedefs_, value_scope);
  if (!folded) return;
  pd.resolved_value = *folded;
  pd.is_resolved = true;
}

static void ResolveParamPortTypeRef(
    const ModuleDecl* decl, size_t i, bool has_param_type,
    const std::function<void(DataType&)>& resolve) {
  if (has_param_type) resolve(const_cast<DataType&>(decl->param_types[i]));
}

void Elaborator::DeclareTypeParamPortEnums(const ModuleDecl& decl,
                                           std::size_t i,
                                           const RtlirParamDecl& param,
                                           const ParamList& params,
                                           RtlirModule* mod) {
  if (!param.is_type_param) return;
  DeclareTypeParamEnums(decl.param_types[i], param,
                        FindParamOverride(params, param.name) != nullptr, mod);
}

void Elaborator::BindTypeParamDims(std::string_view name,
                                   const std::vector<Expr*>& dims) {
  if (dims.empty()) {
    td_array_dims_.erase(name);
    return;
  }
  td_array_dims_[name] = dims;
  aggregate_typedef_names_.insert(name);
}

void Elaborator::BindTypeParamPort(const ModuleDecl& decl, std::size_t i,
                                   const AssignedTypes& assigned,
                                   RtlirParamDecl& param, RtlirModule* mod) {
  if (!param.is_type_param) return;
  auto given = assigned.find(param.name);
  if (given != assigned.end()) {
    BindTypeParamDims(param.name,
                      WithTypedefDims(given->second.resolved.element,
                                      given->second.resolved.dims,
                                      {typedefs_, td_array_dims_, class_names_})
                          .dims);
    return;
  }
  const Expr* ref = decl.param_types.at(i).type_ref_expr;
  if (ref == nullptr) return;
  AssignedType referenced = TypeAssignedIn(mod, ref, param.loc);
  if (referenced.written.kind == DataTypeKind::kImplicit) {
    ReportTypeParamSetToNoType(param.name, param.loc, diag_);
    return;
  }
  typedefs_[param.name] = referenced.resolved.element;
  BindTypeParamDims(param.name, referenced.resolved.dims);
  param.resolved_type = arena_.Create<DataType>(referenced.written);
}

void Elaborator::ElaborateParamPortList(const ModuleDecl* decl,
                                        const ParamList& params,
                                        RtlirModule* mod) {
  TypeParamValueCtx tp_ctx{typedefs_, class_names_, diag_};
  const auto kWrittenTypes = std::exchange(pending_type_param_types_, {});
  const TypeShapeTables kShapeTables{typedefs_, td_array_dims_, class_names_};
  const InstanceParamAssignments kAssigns{
      params, RegisteredModuleScope(), RegisteredModule(),
      InnermostScope(RegisteredGenPrefixes())};
  for (size_t i = 0; i < decl->params.size(); ++i) {
    const auto& [pname, pval] = decl->params[i];
    bool has_param_type = i < decl->param_types.size() &&
                          decl->type_param_names.count(pname) == 0;
    ResolveParamPortTypeRef(decl, i, has_param_type, [&](DataType& dt) {
      ResolveTypeRef(dt, decl->range.start, mod);
      EmitInPlaceEnumMembers(dt, pname, decl->param_port_locs[i], mod);
    });
    auto scope = BuildParamScope(mod);
    RtlirParamDecl pd = BuildParamDeclShell(
        decl, i, {typedefs_, scope, real_param_names_, kWrittenTypes, arena_},
        has_param_type);
    BindTypeParamPort(*decl, i, kWrittenTypes, pd, mod);
    RecordTypeParamActual(pd, mod->params, typedefs_, arena_);
    const DataType* param_type =
        has_param_type ? &decl->param_types[i] : nullptr;
    const bool kUnpacked = decl->param_port_unpacked_dims.count(pname) != 0;
    ApplyParamOverride(pd, kAssigns, pname, typedefs_, arena_);
    DeclareTypeParamPortEnums(*decl, i, pd, params, mod);
    ReportInstanceOverrideType(pd, kAssigns, {kShapeTables, scope, unit_},
                               diag_);
    CheckDollarOverride(kAssigns, {pname, nullptr, param_type, kUnpacked},
                        kShapeTables, diag_);
    if (!pd.is_resolved && !pd.from_override && pval) {
      bool refers_to_unbounded = pval->kind == ExprKind::kIdentifier &&
                                 RefersToUnboundedParam(mod, pval->text);
      bool contains_dollar = ContainsDollarSubexpr(pval);
      ParamValueExpr val{
          pval,           pname,      refers_to_unbounded, contains_dollar,
          has_param_type, param_type, kUnpacked,           kShapeTables};
      ParamRangeRegistryGuard default_guard(mod);
      ResolveUnresolvedParamValue(pd, val, scope, diag_);
      if (pd.is_real_value) real_param_names_.insert(pname);
    }
    if (pval && has_param_type && !pd.from_override) {
      ParamRangeRegistryGuard param_range_guard(mod);
      RecordStringParamValue(pd, pval, param_type, arena_);
    }
    CheckTypeParamValueAssignable(decl, i, pval, scope, tp_ctx);
    ResolvePackedStructParam(pd, param_type, pval, scope);
    mod->params.push_back(pd);
  }
}

static const InstanceParamAssignments* g_body_param_assignments = nullptr;

BodyParamAssignmentsGuard::BodyParamAssignmentsGuard(
    const InstanceParamAssignments* assigns)
    : prev_(g_body_param_assignments) {
  g_body_param_assignments = assigns;
}

BodyParamAssignmentsGuard::~BodyParamAssignmentsGuard() {
  g_body_param_assignments = prev_;
}

const InstanceParamAssignments* BodyParamAssignments() {
  return g_body_param_assignments;
}

std::vector<std::string_view> OverridableParamNames(const ModuleDecl* decl) {
  std::vector<std::string_view> names;
  for (const auto& [pname, pval] : decl->params) {
    if (decl->localparam_port_names.count(pname) > 0) continue;
    names.push_back(pname);
  }
  if (decl->has_param_port_list) return names;
  for (const ModuleItem* item : decl->items) {
    if (item->kind != ModuleItemKind::kParamDecl || item->is_localparam)
      continue;
    names.push_back(item->name);
  }
  return names;
}

static const ModuleItem* BodyParamDecl(const ModuleDecl* decl,
                                       std::string_view pname) {
  for (const ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kParamDecl && item->name == pname)
      return item;
  }
  return nullptr;
}

static bool IsBodyTypeParam(const ModuleDecl* decl, std::string_view pname) {
  if (decl->has_param_port_list) return false;
  const ModuleItem* item = BodyParamDecl(decl, pname);
  return item != nullptr && !item->is_localparam &&
         item->data_type.kind == DataTypeKind::kVoid;
}

const Expr* UntypedPattern(const Expr* value) {
  bool typed = value->kind == ExprKind::kCast &&
               value->lhs->kind == ExprKind::kAssignmentPattern;
  return typed ? value->lhs : value;
}

static bool MayHoldAggregate(const ModuleDecl* decl, std::string_view pname) {
  if (decl->param_port_unpacked_dims.count(pname) > 0) return true;
  const DataType* type = nullptr;
  size_t ports = std::min(decl->params.size(), decl->param_types.size());
  for (size_t i = 0; i < ports; ++i)
    if (decl->params[i].first == pname) type = &decl->param_types[i];
  if (const ModuleItem* item = BodyParamDecl(decl, pname)) {
    if (!item->unpacked_dims.empty()) return true;
    type = &item->data_type;
  }
  return type != nullptr && (type->kind == DataTypeKind::kStruct ||
                             type->kind == DataTypeKind::kUnion ||
                             type->kind == DataTypeKind::kNamed);
}

AppliedTypeParams Elaborator::ApplyTypeParams(TypeParamAssignments from,
                                              const ModuleDecl* child_decl,
                                              const RtlirModule* mod) {
  from.type_of = [&](const Expr* value, SourceLoc loc) {
    return TypeAssignedIn(mod, value, loc);
  };
  from.default_type = [&](const DataType& type) {
    UnpackedArrayType shape =
        WithTypedefDims(type, {}, {typedefs_, td_array_dims_, class_names_});
    shape.element = InInstantiatingScope(std::move(shape.element), typedefs_);
    return shape;
  };
  AppliedTypeParams applied =
      ApplyChildTypeParams(from, child_decl, typedefs_, diag_);
  ReportChildTypeParamsOutsideRestrictions(
      child_decl, applied, {typedefs_, unit_, class_names_}, diag_);
  return applied;
}

void Elaborator::ReadTypesAssigned(ParamList& params,
                                   const ModuleDecl& child_decl,
                                   const RtlirModule* mod) {
  for (ParamOverride& given : params) {
    if (!IsBodyTypeParam(&child_decl, given.name)) continue;
    given.assigned_type = arena_.Create<AssignedType>(
        TypeAssignedIn(mod, given.value_expr, given.value_expr->range.start));
  }
}

bool Elaborator::NamesNoType(const DataType& type,
                             const RtlirModule* mod) const {
  if (type.kind != DataTypeKind::kNamed || !type.scope_name.empty())
    return false;
  const std::string_view kName = type.type_name;
  return !typedefs_.contains(kName) && !class_names_.contains(kName) &&
         VisibleCovergroup(kName, mod, unit_) == nullptr;
}

AssignedType Elaborator::TypeAssignedIn(const RtlirModule* mod,
                                        const Expr* value, SourceLoc loc) {
  AssignedType assigned;
  if (value->kind == ExprKind::kTypeRef) {
    CheckTypeRefArgInner(value->lhs, loc, mod);
    std::optional<UnpackedArrayType> referenced =
        TypeRefOperandArray(value, mod);
    if (!referenced || NamesNoType(referenced->element, mod)) return assigned;
    assigned.written = std::move(referenced->element);
    assigned.resolved.dims = std::move(referenced->dims);
  } else {
    assigned.written = TypeParamOverrideToDataType(value, unit_, diag_, loc);
  }
  if (assigned.written.kind == DataTypeKind::kImplicit) return assigned;
  assigned.resolved =
      WithTypedefDims(assigned.written, std::move(assigned.resolved.dims),
                      {typedefs_, td_array_dims_, class_names_});
  DataType& element = assigned.resolved.element;
  element = InInstantiatingScope(std::move(element), typedefs_);
  const ScopeMap kScope = BuildParamScope(mod);
  FoldTypeDims(assigned.written, kScope, arena_);
  FoldTypeDims(element, kScope, arena_);
  FoldUnpackedDims(assigned.resolved.dims, kScope, arena_);
  return assigned;
}

static void PushUnfoldedValue(std::string_view pname, const Expr* pexpr,
                              Elaborator::ParamList& child_params) {
  Elaborator::ParamOverride ovr{pname, 0, pexpr};
  ovr.unfolded = true;
  child_params.push_back(ovr);
}

bool PushInstParamAssignment(const ModuleDecl* child_decl,
                             std::string_view pname, const Expr* pexpr,
                             const ScopeMap& parent_scope,
                             Elaborator::ParamList& child_params) {
  bool dollar =
      ContainsDollar(pexpr) && child_decl->type_param_names.count(pname) == 0;
  if (dollar || IsBodyTypeParam(child_decl, pname)) {
    child_params.push_back({pname, 0, pexpr});
    return true;
  }
  bool aggregate = MayHoldAggregate(child_decl, pname);
  if (aggregate &&
      UntypedPattern(pexpr)->kind == ExprKind::kAssignmentPattern) {
    PushUnfoldedValue(pname, pexpr, child_params);
    return true;
  }
  if (auto real = RealOverrideValue(pexpr, parent_scope)) {
    Elaborator::ParamOverride ovr{pname, RoundRealToInteger(*real), pexpr};
    ovr.real = real;
    child_params.push_back(ovr);
    return true;
  }
  if (auto val = ConstEvalInt(pexpr, parent_scope)) {
    child_params.push_back({pname, *val, pexpr});
    return true;
  }
  if (aggregate || child_decl->type_param_names.count(pname) == 0)
    PushUnfoldedValue(pname, pexpr, child_params);
  return aggregate;
}

static bool IsLocalParamOf(const ModuleDecl* decl, std::string_view pname) {
  if (decl->localparam_port_names.count(pname) > 0) return true;
  const ModuleItem* item = BodyParamDecl(decl, pname);
  return item != nullptr && (item->is_localparam || decl->has_param_port_list);
}

static bool ConfigParamRefused(
    const ModuleDecl* child_decl,
    const std::unordered_set<std::string_view>& overridable,
    std::string_view pname, SourceLoc loc, DiagEngine& diag) {
  if (IsLocalParamOf(child_decl, pname)) {
    diag.Error(loc,
               std::format("configuration cannot override a local parameter: "
                           "'{}' of module '{}'",
                           pname, child_decl->name),
               Subclause("6.20.4"));
    return true;
  }
  if (overridable.count(pname) > 0) return false;
  diag.Error(
      loc,
      std::format("module '{}' has no parameter '{}'", child_decl->name, pname),
      Subclause("23.10.2.2"));
  return true;
}

std::vector<std::pair<std::string_view, Expr*>> AssignableConfigParams(
    const ModuleDecl* child_decl,
    const std::vector<std::pair<std::string_view, Expr*>>& override_params,
    SourceLoc loc, DiagEngine& diag) {
  const std::vector<std::string_view> kNames =
      OverridableParamNames(child_decl);
  const std::unordered_set<std::string_view> kOverridable(kNames.begin(),
                                                          kNames.end());
  std::vector<std::pair<std::string_view, Expr*>> assignable;
  assignable.reserve(override_params.size());
  for (const auto& entry : override_params) {
    if (ConfigParamRefused(child_decl, kOverridable, entry.first, loc, diag))
      continue;
    assignable.push_back(entry);
  }
  return assignable;
}

}  // namespace delta
