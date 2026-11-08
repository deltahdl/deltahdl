#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/expr_substitute.h"
#include "simulator/assoc_element.h"
#include "simulator/class_event_property.h"
#include "simulator/class_object.h"
#include "simulator/class_specialization.h"
#include "simulator/clocking.h"
#include "simulator/covergroup_instance.h"
#include "simulator/eval_array.h"
#include "simulator/eval_call_result.h"
#include "simulator/eval_class_array_handles.h"
#include "simulator/eval_class_params.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_function_hier.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_member_path.h"
#include "simulator/eval_semaphore.h"
#include "simulator/eval_string.h"
#include "simulator/eval_struct_property.h"
#include "simulator/evaluation.h"
#include "simulator/modport_expression.h"
#include "simulator/sequence_monitor.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/struct_string_member.h"
#include "simulator/virtual_interface.h"

namespace delta {

bool ExtractMethodCallParts(const Expr* expr, MethodCallParts& out) {
  if (!expr->lhs || expr->lhs->kind != ExprKind::kMemberAccess) return false;
  auto* access = expr->lhs;
  if (!access->lhs || access->lhs->kind != ExprKind::kIdentifier) return false;
  if (!access->rhs || access->rhs->kind != ExprKind::kIdentifier) return false;
  out.var_name = access->lhs->text;
  out.method_name = access->rhs->text;
  out.loc = access->rhs->range.start;
  return true;
}

static Logic4Vec EvalReplicateInner(const Expr* expr, SimContext& ctx,
                                    Arena& arena) {
  std::vector<Logic4Vec> parts;
  uint32_t width = 0;
  bool is_string = false;
  for (auto* elem : expr->elements) {
    parts.push_back(EvalExpr(elem, ctx, arena));
    is_string = is_string || parts.back().is_string;
    width += parts.back().width;
  }
  Logic4Vec inner = AssembleConcatParts(parts, width, arena);
  inner.is_string = is_string;
  return inner;
}

Logic4Vec EvalReplicate(const Expr* expr, SimContext& ctx, Arena& arena) {
  uint32_t count = static_cast<uint32_t>(
      EvalExpr(expr->repeat_count, ctx, arena).ToUint64());
  if (count == 0) {
    EvalReplicateInner(expr, ctx, arena);
    return MakeLogic4Vec(arena, 0);
  }
  if (expr->elements.empty()) return MakeLogic4Vec(arena, 0);
  Logic4Vec inner = EvalReplicateInner(expr, ctx, arena);
  std::vector<Logic4Vec> copies(count, inner);
  Logic4Vec result = AssembleConcatParts(copies, inner.width * count, arena);
  result.is_string = inner.is_string;
  return result;
}

static bool TryCollectionAccess(std::string_view base, std::string_view field,
                                SimContext& ctx, Arena& arena, Logic4Vec& out) {
  if (TryEvalArrayProperty(base, field, ctx, arena, out)) return true;
  if (TryExecArrayPropertyStmt(base, field, ctx, arena)) {
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  if (TryEvalQueueProperty(base, field, ctx, arena, out)) return true;
  if (TryExecQueuePropertyStmt(base, field, ctx, arena)) {
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  if (TryEvalAssocProperty(base, field, ctx, arena, out)) return true;
  if (TryExecAssocPropertyStmt(base, field, ctx, arena)) {
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  if (TryEvalStringProperty(base, field, ctx, arena, out)) return true;
  return false;
}

struct MemberAccess {
  std::string_view base_name;
  std::string_view field_name;
  Variable* base_var;
  SimContext& ctx;
  Arena& arena;
  SourceLoc loc;
};

static Logic4Vec ReadClassField(ClassObject* obj,
                                const ClassTypeInfo* declared_type,
                                std::string_view field, Arena& arena) {
  if (declared_type)
    return obj->GetPropertyForType(field, declared_type, arena);
  return obj->GetProperty(field, arena);
}

Logic4Vec ResolveClassFieldChain(ClassObject* obj,
                                 const ClassTypeInfo* declared_type,
                                 std::string_view field_path, SimContext& ctx,
                                 Arena& arena) {
  auto dot = field_path.find('.');
  if (dot == std::string_view::npos) {
    return ReadClassField(obj, declared_type, field_path, arena);
  }
  auto first = field_path.substr(0, dot);
  auto rest = field_path.substr(dot + 1);
  Logic4Vec handle_val = ReadClassField(obj, declared_type, first, arena);
  PropertyFieldWindow window = ResolveClassPropertyField(
      declared_type ? declared_type : obj->type, field_path, ctx);
  if (window.valid) {
    return MemberValueOf(
        ExtractBitField(arena, handle_val, window.bit_offset, window.width),
        window.member_kind, arena);
  }
  auto* next_obj = ctx.GetClassObject(handle_val.ToUint64());
  if (!next_obj) return ReadClassField(obj, declared_type, field_path, arena);
  return ResolveClassFieldChain(next_obj, nullptr, rest, ctx, arena);
}

static bool TryClassPropertyAccess(const MemberAccess& ma, Logic4Vec& out) {
  Variable* base_var = ma.base_var;
  if (!base_var) return false;
  auto* obj = ma.ctx.GetClassObject(base_var->value.ToUint64());
  if (!obj) return false;
  const ClassTypeInfo* declared_type = nullptr;
  auto declared = ma.ctx.GetVariableClassType(ma.base_name);
  if (!declared.empty()) declared_type = ma.ctx.FindClassType(declared);
  out = ResolveClassFieldChain(obj, declared_type, ma.field_name, ma.ctx,
                               ma.arena);
  return true;
}

static bool TryClassEnumAccess(Variable* base_var, std::string_view field_name,
                               SimContext& ctx, Arena& arena, Logic4Vec& out) {
  if (!base_var) return false;
  auto handle = base_var->value.ToUint64();
  auto* obj = ctx.GetClassObject(handle);
  if (!obj || !obj->type) return false;
  auto it = obj->type->enum_members.find(std::string(field_name));
  if (it == obj->type->enum_members.end()) return false;
  out = ClassEnumLiteral(*obj->type, it->first, it->second, arena);
  return true;
}

static bool TryLocalStaticMember(const ClassTypeInfo* cls_type,
                                 std::string_view field_name, Arena& arena,
                                 Logic4Vec& out) {
  auto it = cls_type->static_properties.find(std::string(field_name));
  if (it != cls_type->static_properties.end()) {
    out = it->second;
    return true;
  }
  auto eit = cls_type->enum_members.find(std::string(field_name));
  if (eit != cls_type->enum_members.end()) {
    out = ClassEnumLiteral(*cls_type, eit->first, eit->second, arena);
    return true;
  }
  return false;
}

static bool TryInterfaceStaticMember(const ClassTypeInfo* cls_type,
                                     std::string_view field_name, Arena& arena,
                                     Logic4Vec& out) {
  std::vector<const ClassTypeInfo*> stack;
  if (cls_type->parent && cls_type->parent->is_interface)
    stack.push_back(cls_type->parent);
  for (const auto* ei : cls_type->extended_interfaces) stack.push_back(ei);
  while (!stack.empty()) {
    const auto* cur = stack.back();
    stack.pop_back();
    if (TryLocalStaticMember(cur, field_name, arena, out)) return true;
    if (cur->parent && cur->parent->is_interface) stack.push_back(cur->parent);
    for (const auto* ei : cur->extended_interfaces) stack.push_back(ei);
  }
  return false;
}

static bool TryStaticMemberAccess(std::string_view base_name,
                                  std::string_view field_name, SimContext& ctx,
                                  Arena& arena, Logic4Vec& out) {
  auto* cls_type = ctx.FindClassType(base_name);
  if (!cls_type) return false;
  for (const auto* t = cls_type; t != nullptr; t = t->parent) {
    if (TryLocalStaticMember(t, field_name, arena, out)) return true;
  }
  return cls_type->is_interface &&
         TryInterfaceStaticMember(cls_type, field_name, arena, out);
}

static bool TryThisSuperMember(std::string_view base_name,
                               std::string_view field_name, SimContext& ctx,
                               Arena& arena, Logic4Vec& out) {
  if (base_name == "this") {
    auto* self = ctx.CurrentThis();
    out = self ? ResolveClassFieldChain(self, ctx.CurrentMethodClass(),
                                        field_name, ctx, arena)
               : MakeLogic4Vec(arena, 1);
    return true;
  }
  if (base_name == "super") {
    auto* self = ctx.CurrentThis();
    const ClassTypeInfo* enclosing = ctx.CurrentMethodClass();
    const ClassTypeInfo* super_type =
        enclosing ? enclosing->parent
                  : (self && self->type ? self->type->parent : nullptr);
    if (self && super_type) {
      out = self->GetPropertyForType(field_name, super_type, arena);
    } else {
      out = MakeLogic4Vec(arena, 1);
    }
    return true;
  }
  return false;
}

static bool TryUnionTagMismatch(const MemberAccess& ma,
                                const StructTypeInfo* sinfo, Logic4Vec& out) {
  UnionTagMismatch m =
      FindUnionTagMismatch(ma.base_name, sinfo, ma.field_name, ma.ctx);
  if (!m.found) return false;
  ma.ctx.GetDiag().Error(ma.loc,
                         "run-time error: accessing member '" + m.member +
                             "' of tagged union '" + m.union_name +
                             "' which currently has tag '" + m.tag + "'",
                         Subclause("11.9"));
  out = MakeAllX(ma.arena, sinfo->total_width);
  return true;
}

static bool TryPropertyTagMismatch(const MemberAccess& ma, Logic4Vec& out) {
  std::string name(ma.base_name);
  std::string_view member = ma.field_name;
  if (ma.base_var != nullptr) {
    size_t dot = member.find('.');
    if (dot == std::string_view::npos) return false;
    name += '.';
    name += member.substr(0, dot);
    member = member.substr(dot + 1);
  }
  std::string key;
  const StructTypeInfo* layout = PropertyAggregateLayout(name, ma.ctx, key);
  if (layout == nullptr || !layout->is_union) return false;
  std::string_view tag = ma.ctx.GetVariableTag(key);
  if (tag.empty() || tag == member.substr(0, member.find('.'))) return false;
  ma.ctx.GetDiag().Error(ma.loc,
                         "run-time error: accessing member '" +
                             std::string(member) + "' of tagged union '" +
                             name + "' which currently has tag '" +
                             std::string(tag) + "'",
                         Subclause("11.9"));
  out = MakeAllX(ma.arena, layout->total_width);
  return true;
}

static bool SequenceMatched(std::string_view ep_name, SimContext& ctx) {
  auto* ep = ctx.FindVariable(ep_name);
  if (ep == nullptr) return false;
  return ctx.ConsumeSequenceMatch(ep_name, ep->triggered_ticks,
                                  ctx.CurrentTime().ticks);
}

static bool TryEndPointMethod(std::string_view ep_name,
                              std::string_view field_name, SimContext& ctx,
                              Arena& arena, Logic4Vec& out) {
  if (field_name != "triggered" && field_name != "matched") return false;
  bool reached = field_name == "matched" ? SequenceMatched(ep_name, ctx)
                                         : ctx.IsEventTriggered(ep_name);
  out = MakeLogic4VecVal(arena, 1, reached ? 1u : 0u);
  return true;
}

static bool TrySequenceEndPointMethod(std::string_view base_name,
                                      std::string_view field_name,
                                      SimContext& ctx, Arena& arena,
                                      Logic4Vec& out) {
  return TryEndPointMethod("__seq_" + std::string(base_name), field_name, ctx,
                           arena, out);
}

static bool TryHierarchicalSequenceMethod(const Expr* expr, SimContext& ctx,
                                          Arena& arena, Logic4Vec& out) {
  if (expr->lhs == nullptr || expr->rhs == nullptr ||
      expr->lhs->kind != ExprKind::kMemberAccess) {
    return false;
  }
  std::string ep_name =
      HierarchicalEndPoint(HierarchicalReferenceName(expr->lhs), ctx);
  if (ep_name.empty()) return false;
  return TryEndPointMethod(ep_name, expr->rhs->text, ctx, arena, out);
}

static bool TryEventSequenceMethod(const MemberAccess& ma, Logic4Vec& out) {
  Variable* base_var = ma.base_var;
  SimContext& ctx = ma.ctx;
  Arena& arena = ma.arena;
  std::string_view base_name = ma.base_name;
  std::string_view field_name = ma.field_name;
  if (base_var && base_var->is_event && field_name == "triggered") {
    out = base_var->is_null_event
              ? MakeLogic4VecVal(arena, 1, 0u)
              : MakeLogic4VecVal(arena, 1,
                                 ctx.IsEventTriggered(base_name) ? 1u : 0u);
    return true;
  }
  return !base_var && ctx.FindSequenceDecl(base_name) &&
         TrySequenceEndPointMethod(base_name, field_name, ctx, arena, out);
}

bool TryEvalEventTriggeredCall(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractHandleMethodCallParts(expr, arena, parts)) return false;
  if (parts.method_name != "triggered") return false;
  auto* var = ctx.FindVariable(parts.var_name);
  if (!var || !var->is_event)
    return TryClassEventTriggered(expr, ctx, arena, out);
  out = var->is_null_event
            ? MakeLogic4VecVal(arena, 1, 0u)
            : MakeLogic4VecVal(arena, 1,
                               ctx.IsEventTriggered(parts.var_name) ? 1u : 0u);
  return true;
}

static Logic4Vec ResolveMemberByType(std::string_view base_name,
                                     std::string_view field_name,
                                     SimContext& ctx, Arena& arena,
                                     SourceLoc loc) {
  Logic4Vec out;
  if (TryThisSuperMember(base_name, field_name, ctx, arena, out)) return out;

  auto* base_var = ctx.FindVariable(base_name);
  const StructTypeInfo* sinfo = StructLayoutOfName(base_name, ctx);

  MemberAccess ma{base_name, field_name, base_var, ctx, arena, loc};

  if (base_var && sinfo) {
    if (TryUnionTagMismatch(ma, sinfo, out)) {
      return out;
    }
    if (auto read = StructMemberObjectRead(base_var->value, sinfo, field_name,
                                           ctx, arena)) {
      return *read;
    }
    return ExtractStructField(base_var->value, sinfo, field_name, arena);
  }
  if (TryPropertyTagMismatch(ma, out)) return out;

  if (TryEventSequenceMethod(ma, out)) {
    return out;
  }

  if (TryClassEnumAccess(base_var, field_name, ctx, arena, out)) return out;
  if (TryClassPropertyAccess(ma, out)) return out;
  if (TryCollectionAccess(base_name, field_name, ctx, arena, out)) return out;
  if (TryStaticMemberAccess(base_name, field_name, ctx, arena, out)) return out;
  if (TryClockvarMemberAccess(base_name, field_name, ctx, arena, out))
    return out;
  if (TryImplicitThisHandleMember(base_name, field_name, ctx, arena, out))
    return out;
  return MakeLogic4Vec(arena, 1);
}

static Logic4Vec ReadReferencedVariable(const Variable& var, SimContext& ctx) {
  const Logic4Vec* sampled =
      ctx.AssertionSamples().ReadWithinProperty(&var, ctx.CurrentTime());
  Logic4Vec val = sampled != nullptr ? *sampled : var.value;
  val.is_signed = var.is_signed;
  return val;
}

static bool TryVirtualInterfaceMember(const Expr* expr, SimContext& ctx,
                                      Arena& arena, Logic4Vec& out) {
  VirtualInterfaceBase base =
      ResolveVirtualInterfaceBaseExpr(expr->lhs, ctx, arena);
  std::string inner;
  if (!base.is_virtual_interface) {
    base = ResolveVirtualInterfaceInnerPath(expr, ctx, arena, inner);
  }
  if (!base.is_virtual_interface) return false;
  if (base.handle == kNullVirtualInterface) {
    ReportNullVirtualInterface(expr->range.start, ctx);
    out = MakeLogic4Vec(arena, 1);
    return true;
  }
  std::string_view field =
      (expr->rhs && expr->rhs->kind == ExprKind::kIdentifier)
          ? expr->rhs->text
          : std::string_view(expr->text);
  if (!inner.empty()) field = inner;
  auto* tv =
      ctx.FindVariable(VirtualInterfaceComponentName(base.handle, field, ctx));
  out = tv ? ReadReferencedVariable(*tv, ctx) : MakeLogic4Vec(arena, 1);
  return true;
}

static size_t ValueParamPosition(const ClassDecl& decl, std::string_view name) {
  if (decl.type_param_names.count(name)) return decl.params.size();
  for (size_t i = 0; i < decl.params.size(); ++i) {
    if (decl.params[i].first == name) return i;
  }
  return decl.params.size();
}

static const Expr* FindSpecializationOverride(const Expr& base,
                                              const ClassDecl& decl,
                                              std::string_view name) {
  size_t pos = ValueParamPosition(decl, name);
  if (pos == decl.params.size()) return nullptr;
  const auto& elems = base.elements;
  const auto& names = base.arg_names;
  for (size_t j = 0; j < elems.size(); ++j) {
    if (j < names.size() && !names[j].empty() && names[j] == name && elems[j])
      return elems[j];
  }
  bool ordered = names.empty() || (pos < names.size() && names[pos].empty());
  if (ordered && pos < elems.size()) return elems[pos];
  return nullptr;
}

static Logic4Vec SizedSpecializationActual(const Expr& access,
                                           const ClassDecl& decl,
                                           const Expr* value, SimContext& ctx,
                                           Arena& arena) {
  const Expr& base = *access.lhs;
  ClassParamSizer sizer(&decl);
  if (const ClassTypeInfo* spec = ScopeNamedSpecialization(&base, ctx, arena))
    sizer.UseTypeActuals(spec->param_actuals);
  size_t pos = ValueParamPosition(decl, access.rhs->text);
  for (size_t i = 0; i < pos; ++i) {
    std::string_view earlier = decl.params[i].first;
    if (decl.type_param_names.count(earlier) != 0 ||
        decl.param_port_unpacked_dims.count(earlier) != 0)
      continue;
    const Expr* e = FindSpecializationOverride(base, decl, earlier);
    if (e == nullptr) e = decl.params[i].second;
    if (e != nullptr) sizer.Value(i, e, ctx, arena);
  }
  return sizer.Value(pos, value, ctx, arena);
}

static bool TryParameterizedScopeParam(const Expr* expr, SimContext& ctx,
                                       Arena& arena, Logic4Vec& out) {
  if (!expr->lhs || expr->lhs->kind != ExprKind::kIdentifier ||
      !expr->lhs->has_param_spec || expr->lhs->elements.empty())
    return false;
  if (!expr->rhs || expr->rhs->kind != ExprKind::kIdentifier) return false;
  const ClassTypeInfo* cls = ctx.FindClassType(expr->lhs->text);
  if (!cls || !cls->decl) return false;
  const Expr* override_expr =
      FindSpecializationOverride(*expr->lhs, *cls->decl, expr->rhs->text);
  if (override_expr == nullptr) return false;
  out = SizedSpecializationActual(*expr, *cls->decl, override_expr, ctx, arena);
  return true;
}

static bool ReadsAMonitorEndPoint(const Expr* expr, SimContext& ctx) {
  if (expr->lhs == nullptr || expr->rhs == nullptr ||
      (expr->rhs->text != "triggered" && expr->rhs->text != "matched")) {
    return false;
  }
  if (expr->lhs->kind == ExprKind::kCall) {
    return ctx.FindSequenceDecl(expr->lhs->callee) != nullptr;
  }
  return expr->lhs->kind == ExprKind::kIdentifier &&
         (expr->lhs->property_actual != nullptr ||
          !ctx.FindSequenceInstanceEndpoint(expr->lhs).empty());
}

static bool TryInstanceTriggered(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out) {
  if (!ReadsAMonitorEndPoint(expr, ctx)) return false;
  std::string_view ep_name = ctx.FindSequenceInstanceEndpoint(expr->lhs);
  bool triggered = !ep_name.empty() && (expr->rhs->text == "matched"
                                            ? SequenceMatched(ep_name, ctx)
                                            : ctx.IsEventTriggered(ep_name));
  out = MakeLogic4VecVal(arena, 1, triggered ? 1u : 0u);
  return true;
}

static bool TryCheckerFormalEndPoint(const Expr* expr, SimContext& ctx,
                                     Arena& arena, Logic4Vec& out) {
  if (expr->lhs == nullptr || expr->rhs == nullptr ||
      expr->lhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  const ActualsByFormal* actuals =
      ctx.CheckerActuals(ctx.ActiveInstancePrefix());
  if (actuals == nullptr) return false;
  auto it = actuals->find(expr->lhs->text);
  if (it == actuals->end()) return false;
  std::string_view ep_name = ctx.FindSequenceInstanceEndpoint(it->second);
  return !ep_name.empty() &&
         TryEndPointMethod(ep_name, expr->rhs->text, ctx, arena, out);
}

static bool TryMemberSelectThatIsNoRead(const Expr* expr, SimContext& ctx,
                                        Arena& arena, Logic4Vec& out) {
  if (TryInstanceTriggered(expr, ctx, arena, out)) return true;
  if (TryCheckerFormalEndPoint(expr, ctx, arena, out)) return true;
  if (TryHierarchicalSequenceMethod(expr, ctx, arena, out)) return true;
  if (TryEvalArrayReductionWithClause(expr, ctx, arena, out)) return true;
  if (TryExecArrayOrderingWithClauseStmt(expr, ctx, arena)) {
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  return TryParameterizedScopeParam(expr, ctx, arena, out) ||
         TryScopeSpecializationStaticMember(expr, ctx, arena, out) ||
         TryEvalProcessMethodWithoutArgs(expr, ctx, arena, out) ||
         TryEvalEnumMethodWithoutArgs(expr, ctx, arena, out) ||
         TryEvalSemaphoreMethodCall(expr, ctx, arena, out) ||
         TryClassEventTriggered(expr, ctx, arena, out);
}

static bool TryObjectMemberRead(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out) {
  return TryEvalAssocMemberField(expr, ctx, arena, out) ||
         TryEvalElementObjectMember(expr, ctx, arena, out) ||
         TryEvalCallResultMember(expr, ctx, arena, out) ||
         TryPackageClassStaticMember(expr, ctx, arena, out) ||
         TryStaticHandleMember(expr, ctx, arena, out);
}

static bool TryLocalScopeQualifier(std::string& resolved, SimContext& ctx,
                                   Logic4Vec& out) {
  constexpr std::string_view kLocalScopePrefix = "local.";
  if (!std::string_view(resolved).starts_with(kLocalScopePrefix)) return false;
  if (const Variable* bound = ctx.FindLocalVariable(resolved)) {
    out = bound->value;
    return true;
  }
  resolved = resolved.substr(kLocalScopePrefix.size());
  return false;
}

static bool HeadNamesAnInstance(const Expr* expr, SimContext& ctx) {
  const Expr* head = expr;
  while (head->kind == ExprKind::kMemberAccess ||
         head->kind == ExprKind::kSelect) {
    head = head->kind == ExprKind::kSelect ? head->base : head->lhs;
    if (head == nullptr) return false;
  }
  return head->kind == ExprKind::kIdentifier &&
         ctx.FindVariable(head->text) == nullptr &&
         ctx.FindArrayInfo(head->text) == nullptr;
}

static Variable* FindReferencedVariable(const Expr* expr,
                                        const std::string& resolved,
                                        SimContext& ctx, Arena& arena) {
  std::string rooted = RootedReferenceKey(expr);
  auto* var = rooted.empty() ? nullptr : ctx.FindVariable(rooted);
  if (var == nullptr) var = ctx.FindVariable(resolved);
  if (var == nullptr && HeadNamesAnInstance(expr, ctx)) {
    var = ctx.FindVariable(EvaluatedHierarchicalPath(expr, ctx, arena));
  }
  return var;
}

static bool TryCastMemberRead(const Expr* expr, SimContext& ctx, Arena& arena,
                              Logic4Vec& out) {
  const Expr* base = expr->lhs;
  while (base->kind == ExprKind::kMemberAccess) base = base->lhs;
  if (base->kind != ExprKind::kCast) return false;
  const StructTypeInfo* layout = ctx.FindStructType(CastTypeKey(base, ctx));
  if (layout == nullptr) return false;
  std::string path(expr->rhs->text);
  for (const Expr* e = expr->lhs; e != base; e = e->lhs) {
    path.insert(0, std::string(e->rhs->text) + ".");
  }
  out = ExtractStructField(EvalExpr(base, ctx, arena), layout, path, arena);
  return true;
}

static bool TryMemberOfAValue(const Expr* expr, SimContext& ctx, Arena& arena,
                              Logic4Vec& out) {
  return TryCastMemberRead(expr, ctx, arena, out) ||
         TryStaticStructMember(expr, ctx, arena, out) ||
         TryContainerElementMember(expr, ctx, arena, out);
}

Logic4Vec EvalMemberAccess(const Expr* expr, SimContext& ctx, Arena& arena) {
  Logic4Vec out;
  if (TryMemberOfAValue(expr, ctx, arena, out)) return out;
  if (TryEvalStringMethodWithoutParens(expr, ctx, arena, out)) return out;
  if (TryMemberSelectThatIsNoRead(expr, ctx, arena, out)) return out;

  if (TryClockvarPathRead(expr, ctx, arena, out)) return out;
  if (TryVirtualInterfaceMember(expr, ctx, arena, out)) return out;
  if (TryModportExpressionRead(expr, ctx, arena, out)) return out;

  if (TryObjectMemberRead(expr, ctx, arena, out)) return out;
  if (TryEvalCovergroupOptionRead(expr, ctx, arena, out)) return out;

  auto resolved = HierarchicalReferenceName(expr);
  if (TryLocalScopeQualifier(resolved, ctx, out)) return out;
  if (auto* var = FindReferencedVariable(expr, resolved, ctx, arena)) {
    return ReadReferencedVariable(*var, ctx);
  }
  if (TryInterfaceInstancePathHandle(expr, ctx, arena, out)) return out;

  auto dot = MemberPathSplit(resolved, ctx);
  if (dot == std::string::npos) return MakeLogic4Vec(arena, 1);
  auto base_name = std::string_view(resolved).substr(0, dot);
  if (ctx.FindVariable(base_name) == nullptr) {
    if (Variable* local = FunctionStaticLocal(expr, ctx, arena)) {
      return local->value;
    }
  }
  auto field_name = std::string_view(resolved).substr(dot + 1);
  return ResolveMemberByType(base_name, field_name, ctx, arena,
                             expr->range.start);
}

}  // namespace delta
