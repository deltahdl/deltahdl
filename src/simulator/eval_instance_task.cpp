#include "simulator/eval_instance_task.h"

#include <string>
#include <string_view>
#include <unordered_map>

#include "common/arena.h"
#include "common/source_loc.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "simulator/class_object.h"
#include "simulator/class_specialization.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_array_element_queue.h"
#include "simulator/eval_assoc_class_handles.h"
#include "simulator/eval_class_array_handles.h"
#include "simulator/eval_class_scope_types.h"
#include "simulator/eval_function_hier.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_member_path.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

namespace delta {

static bool ResolveStaticTaskByScope(const Expr* expr, SimContext& ctx,
                                     Arena& arena, InstanceMethodInfo& call) {
  const Expr* access = expr->kind == ExprKind::kCall ? expr->lhs : expr;
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      !access->is_scope_resolution || access->rhs == nullptr ||
      access->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  const ClassTypeInfo* cls =
      access->lhs->elements.empty()
          ? ctx.FindClassType(ScopedClassKey(access->lhs, arena))
          : ScopeNamedSpecialization(access->lhs, ctx, arena);
  if (cls == nullptr) return false;
  auto it = cls->methods.find(std::string(access->rhs->text));
  if (it == cls->methods.end()) return false;
  call.obj = nullptr;
  call.method = it->second;
  call.owner = cls;
  return true;
}

static bool IsPackageQualifiedName(const Expr* expr) {
  return expr->kind == ExprKind::kMemberAccess && expr->is_scope_resolution &&
         expr->lhs != nullptr && expr->rhs != nullptr &&
         expr->lhs->kind == ExprKind::kIdentifier &&
         expr->rhs->kind == ExprKind::kIdentifier;
}

bool ExtractHandleAccessParts(const Expr* access, Arena& arena,
                              MethodCallParts& out) {
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      access->lhs == nullptr || access->rhs == nullptr ||
      access->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  const Expr* handle = access->lhs;
  if (handle->kind == ExprKind::kIdentifier) {
    out.var_name = handle->text;
  } else if (!access->is_scope_resolution && IsPackageQualifiedName(handle)) {
    auto* key = arena.Create<std::string>(std::string(handle->lhs->text) + "." +
                                          std::string(handle->rhs->text));
    out.var_name = *key;
  } else {
    return false;
  }
  out.method_name = access->rhs->text;
  out.loc = access->rhs->range.start;
  return true;
}

bool ExtractHandleMethodCallParts(const Expr* expr, Arena& arena,
                                  MethodCallParts& out) {
  return expr != nullptr && ExtractHandleAccessParts(expr->lhs, arena, out);
}

static bool ResolveMethodOnRunningObject(std::string_view name, SimContext& ctx,
                                         InstanceMethodInfo& call) {
  ClassObject* self = ctx.CurrentThis();
  if (self == nullptr) return false;
  const ClassTypeInfo* enclosing = ctx.CurrentMethodClass();
  if (enclosing == nullptr) enclosing = self->type;
  call.obj = self;
  call.method = self->ResolveVirtualMethod(name, &call.owner);
  if (call.method == nullptr) {
    call.method = self->ResolveMethodForType(name, enclosing, &call.owner);
  }
  return call.method != nullptr;
}

static bool ResolveMethodThroughSuper(std::string_view name, SimContext& ctx,
                                      InstanceMethodInfo& call) {
  ClassObject* self = ctx.CurrentThis();
  if (self == nullptr) return false;
  const ClassTypeInfo* enclosing = ctx.CurrentMethodClass();
  if (enclosing == nullptr) enclosing = self->type;
  if (enclosing == nullptr || enclosing->parent == nullptr) return false;
  call.obj = self;
  call.method =
      self->ResolveMethodForType(name, enclosing->parent, &call.owner);
  return call.method != nullptr;
}

static bool ResolveMethodByParts(const MethodCallParts& parts, SimContext& ctx,
                                 InstanceMethodInfo& call) {
  if (parts.var_name == "super") {
    return ResolveMethodThroughSuper(parts.method_name, ctx, call);
  }
  return ResolveInstanceMethod(parts, ctx, call);
}

static bool ResolveMethodOnStaticHandle(const Expr* access, SimContext& ctx,
                                        Arena& arena,
                                        InstanceMethodInfo& call) {
  StaticPropertyRef ref;
  if (!ResolveStaticPropertyBase(access->lhs, ctx, arena, ref)) return false;
  std::string_view declared_key;
  ClassObject* obj = StaticPropertyObject(ref, ctx, &declared_key);
  if (obj == nullptr) return false;
  return ResolveMethodByDeclaredClass(obj, declared_key, access->rhs->text, ctx,
                                      call);
}

static bool HeldHandleProperty(const Expr* base, SimContext& ctx,
                               Arena& arena) {
  if (base->kind != ExprKind::kMemberAccess || base->is_scope_resolution ||
      base->lhs == nullptr || base->rhs == nullptr ||
      base->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  const ClassObject* owner =
      ctx.GetClassObject(EvalExpr(base->lhs, ctx, arena).ToUint64());
  if (owner == nullptr || owner->type == nullptr) return false;
  return !PropertyClassName(owner, owner->type, base->rhs->text, ctx).empty() &&
         !PropertyIsArray(owner->type, base->rhs->text, ctx);
}

static bool ResolveMethodOnEvaluatedBase(const Expr* access, SimContext& ctx,
                                         Arena& arena, InstanceMethodInfo& call,
                                         bool report_null) {
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      access->is_scope_resolution || access->lhs == nullptr ||
      access->rhs == nullptr || access->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  if (ResolveMethodOnStaticHandle(access, ctx, arena, call)) return true;
  if (access->lhs->kind == ExprKind::kIdentifier) return false;
  if (SelectsElementQueue(access->lhs, ctx, arena)) return false;
  ClassObject* obj =
      ctx.GetClassObject(EvalExpr(access->lhs, ctx, arena).ToUint64());
  if (obj == nullptr) {
    if (report_null && HeldHandleProperty(access->lhs, ctx, arena)) {
      ReportNullHandleCall(access->rhs->text, access->rhs->range.start, ctx);
    }
    return false;
  }
  return ResolveMethodByDeclaredClass(obj, {}, access->rhs->text, ctx, call);
}

static bool StartsAtACall(const Expr* base) {
  const Expr* e = base;
  while (e != nullptr && e->kind == ExprKind::kMemberAccess) e = e->lhs;
  return e != nullptr && e->kind == ExprKind::kCall;
}

bool TryEvalMethodOnEvaluatedBase(const Expr* expr, SimContext& ctx,
                                  Arena& arena, Logic4Vec& out) {
  if (expr == nullptr || expr->kind != ExprKind::kCall ||
      expr->lhs == nullptr || expr->lhs->kind != ExprKind::kMemberAccess ||
      StartsAtACall(expr->lhs->lhs)) {
    return false;
  }
  InstanceMethodInfo info;
  if (!ResolveMethodOnEvaluatedBase(expr->lhs, ctx, arena, info, true)) {
    return false;
  }
  out = RunInstanceMethod(info, expr, ctx, arena);
  return true;
}

static bool ResolveMethodNamedBare(const Expr* expr, SimContext& ctx,
                                   Arena& arena, InstanceMethodInfo& call) {
  MethodCallParts parts;
  if (expr->kind == ExprKind::kMemberAccess && !expr->is_scope_resolution) {
    if (ExtractHandleAccessParts(expr, arena, parts)) {
      return ResolveMethodByParts(parts, ctx, call) ||
             ResolveMethodOnStaticHandle(expr, ctx, arena, call);
    }
    return ResolveElementObjectMethod(expr, ctx, arena, call, false) ||
           ResolveAssocElementMethod(expr, ctx, arena, call, false) ||
           ResolveMethodOnEvaluatedBase(expr, ctx, arena, call, false);
  }
  if (expr->kind != ExprKind::kIdentifier) return false;
  return ResolveMethodOnRunningObject(expr->text, ctx, call);
}

static bool ResolveMethodOfStatement(const Expr* expr, SimContext& ctx,
                                     Arena& arena, InstanceMethodInfo& call) {
  if (expr->kind != ExprKind::kCall) {
    return ResolveMethodNamedBare(expr, ctx, arena, call);
  }
  if (expr->lhs != nullptr && expr->lhs->kind == ExprKind::kIdentifier &&
      !expr->callee.empty()) {
    return ResolveMethodOnRunningObject(expr->callee, ctx, call);
  }
  MethodCallParts parts;
  if (ExtractHandleMethodCallParts(expr, arena, parts)) {
    parts.loc = SourceLoc{};
    return ResolveMethodByParts(parts, ctx, call) ||
           ResolveMethodOnStaticHandle(expr->lhs, ctx, arena, call);
  }
  return ResolveElementObjectMethod(expr->lhs, ctx, arena, call, false) ||
         ResolveAssocElementMethod(expr->lhs, ctx, arena, call, false) ||
         ResolveMethodOnEvaluatedBase(expr->lhs, ctx, arena, call, false);
}

bool SetupInstanceTaskCall(const Expr* expr, SimContext& ctx, Arena& arena,
                           InstanceMethodInfo& call) {
  if (expr == nullptr) return false;
  bool through_handle = ResolveMethodOfStatement(expr, ctx, arena, call);
  if (!through_handle && !ResolveStaticTaskByScope(expr, ctx, arena, call))
    return false;
  if (call.method->kind != ModuleItemKind::kTaskDecl) return false;
  if (call.method->is_static_method) {
    call.obj = nullptr;
  } else if (call.obj == nullptr) {
    return false;
  }
  ctx.PushMethodClass(call.owner);
  ctx.PushScope();
  const Expr* scope = expr->lhs != nullptr ? expr->lhs->lhs : nullptr;
  if (call.obj == nullptr && scope != nullptr && !scope->elements.empty()) {
    BindClassParams(call.owner, scope, ctx, arena);
    BindClassScopeTypeActuals(call.owner, scope, ctx, arena);
  }
  ctx.PushThis(call.obj);
  ctx.PushQueueRefFrame();
  ctx.PushAssocRefFrame();
  BodyStaticFrame frame = StaticFrameOfBody(call.method, ctx, arena);
  ctx.PushFuncName(frame.name);
  BindFunctionArgs(call.method, expr, ctx, arena);
  ctx.EnterSubroutineScope(ctx.SubroutinePackage(call.method));
  EnterStaticFrameOwner(ctx, frame.owner);
  return true;
}

void TeardownInstanceTaskCall(const InstanceMethodInfo& call, const Expr* expr,
                              SimContext& ctx, Arena& arena) {
  ctx.PopThis();
  ctx.PopMethodClass();
  LeaveStaticFrameOwner(ctx);
  WritebackOutputArgs(call.method, expr, ctx, arena);
  WritebackQueueRefs(ctx);
  WritebackAssocRefs(ctx);
  ctx.PopFuncName();
  ctx.PopScope();
}

static bool CallableWithoutParens(const ModuleItem* method) {
  if (method == nullptr || method->kind != ModuleItemKind::kFunctionDecl ||
      method->name == "new") {
    return false;
  }
  for (const auto& arg : method->func_args) {
    if (arg.default_value == nullptr) return false;
  }
  return true;
}

static const ModuleItem* MethodOfClassChain(const ClassTypeInfo* cls,
                                            std::string_view name) {
  for (; cls != nullptr; cls = cls->parent) {
    auto it = cls->methods.find(std::string(name));
    if (it != cls->methods.end()) return it->second;
  }
  return nullptr;
}

static const ModuleItem* MethodNamedAsAValue(const Expr* expr, SimContext& ctx,
                                             Arena& arena) {
  if (expr->kind == ExprKind::kIdentifier) {
    const ClassTypeInfo* scope = ctx.CurrentMethodClass();
    if (scope == nullptr && ctx.CurrentThis() != nullptr) {
      scope = ctx.CurrentThis()->type;
    }
    return MethodOfClassChain(scope, expr->text);
  }
  if (expr->kind != ExprKind::kMemberAccess || expr->rhs == nullptr ||
      expr->rhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  if (expr->is_scope_resolution) {
    std::string_view key = ScopedClassKey(expr->lhs, arena);
    if (key.empty()) return nullptr;
    const ClassTypeInfo* cls = ctx.FindClassType(key);
    if (cls == nullptr) cls = ClassNamedByTypeParam(key, ctx, arena);
    return MethodOfClassChain(cls, expr->rhs->text);
  }
  MethodCallParts parts;
  InstanceMethodInfo call;
  if (!ExtractHandleAccessParts(expr, arena, parts)) return nullptr;
  parts.loc = SourceLoc::None();
  if (!ResolveMethodByParts(parts, ctx, call) &&
      !ResolveMethodOnStaticHandle(expr, ctx, arena, call)) {
    return nullptr;
  }
  return call.method;
}

static const Expr* ParenFreeCall(const Expr* name, SimContext& ctx) {
  auto [it, fresh] = ctx.ParenFreeCalls().try_emplace(name, nullptr);
  if (fresh) {
    Arena& arena = ctx.GetArena();
    auto* call = arena.Create<Expr>();
    call->kind = ExprKind::kCall;
    call->callee = name->text;
    call->lhs = arena.Create<Expr>(*name);
    call->range = name->range;
    it->second = call;
  }
  return it->second;
}

static bool TryEvalParenFreeRandomize(const Expr* expr, SimContext& ctx,
                                      Arena& arena, Logic4Vec& out) {
  const bool kMember = expr->kind == ExprKind::kMemberAccess;
  MethodCallParts parts;
  if (kMember && !ExtractHandleAccessParts(expr, arena, parts)) return false;
  if ((kMember ? parts.method_name : expr->text) != "randomize") return false;
  const Expr* call = ParenFreeCall(expr, ctx);
  return TryEvalScopeRandomizeCall(call, ctx, arena, out) ||
         TryEvalRandomizeMethodCall(call, ctx, arena, out);
}

bool TryEvalParenFreeMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out) {
  if (TryEvalParenFreeRandomize(expr, ctx, arena, out)) return true;
  if (!CallableWithoutParens(MethodNamedAsAValue(expr, ctx, arena))) {
    return false;
  }
  out = EvalExpr(ParenFreeCall(expr, ctx), ctx, arena);
  return true;
}

void ExecCallStmtExpr(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr == nullptr) return;
  InstanceMethodInfo call;
  if (ResolveMethodNamedBare(expr, ctx, arena, call)) {
    RunInstanceMethod(call, expr, ctx, arena);
    return;
  }
  EvalExpr(expr, ctx, arena);
}

}  // namespace delta
