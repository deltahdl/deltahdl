// §13.3 with §8.6: a task enabled through an object handle, `h.t(...)`, may
// contain time-controlling statements, so it runs as a coroutine in
// ExecInstanceTaskCall (stmt_exec_class_task.cpp) rather than through the
// synchronous function interpreter ExecClassMethod drives. The frame such a
// call stands in is the one ExecInstanceMethodCall builds -- a scope, `this`,
// the queue and associative reference frames, the defining class as the
// enclosing scope (§8.15) -- and it is set up and torn down here, beside the
// resolution of the handle and the method, so the two callers agree on it.

#include "simulator/eval_instance_task.h"

#include <string>
#include <string_view>

#include "common/arena.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "simulator/class_object.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

namespace delta {

// §8.10 with §8.23: a static task named through the class scope, `C::t(...)`
// or `p::C::t(...)`, resolved to the task and the class whose scope it runs
// in; false for any other call. A static task named through a handle,
// `h.t(...)`, resolves through ResolveInstanceMethod as an instance task does,
// the handle standing for the class (§8.10).
static bool ResolveStaticTaskByScope(const Expr* expr, SimContext& ctx,
                                     Arena& arena, InstanceMethodInfo& call) {
  const Expr* access = expr->lhs;
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      !access->is_scope_resolution || access->rhs == nullptr ||
      access->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  std::string_view class_key = ScopedClassKey(access->lhs, arena);
  if (class_key.empty()) return false;
  const ClassTypeInfo* cls = ctx.FindClassType(class_key);
  if (cls == nullptr) return false;
  auto it = cls->methods.find(std::string(access->rhs->text));
  if (it == cls->methods.end()) return false;
  call.obj = nullptr;
  call.method = it->second;
  call.owner = cls;
  return true;
}

bool SetupInstanceTaskCall(const Expr* expr, SimContext& ctx, Arena& arena,
                           InstanceMethodInfo& call) {
  if (!expr || expr->kind != ExprKind::kCall) return false;
  MethodCallParts parts;
  bool through_handle = ExtractMethodCallParts(expr, parts) &&
                        ResolveInstanceMethod(parts, ctx, call);
  if (!through_handle && !ResolveStaticTaskByScope(expr, ctx, arena, call))
    return false;
  if (call.method->kind != ModuleItemKind::kTaskDecl) return false;
  // §8.10: a static task runs in class scope with no `this`, whether named
  // through the class scope or through a handle, and §13.3 lets its body hold
  // timing controls as any task's may, so it is run as a coroutine here too;
  // handed to the synchronous evaluator, its delay was skipped and its fork
  // never joined. `this` is pushed for an instance task alone, and
  // TeardownInstanceTaskCall pops it for that one alone.
  if (call.method->is_static) {
    call.obj = nullptr;
  } else if (call.obj == nullptr) {
    return false;
  }
  ctx.PushMethodClass(call.owner);
  ctx.PushScope();
  // §8.25: a static task named through a specialization, `C#(42)::t(...)`,
  // runs with the class's parameters bound to the specialization's actuals,
  // as the evaluator's class-scope call binds them (BindClassParams).
  const Expr* scope = expr->lhs != nullptr ? expr->lhs->lhs : nullptr;
  if (call.obj == nullptr && scope != nullptr &&
      scope->kind == ExprKind::kIdentifier && !scope->elements.empty()) {
    BindClassParams(call.owner, scope, ctx, arena);
  }
  if (call.obj != nullptr) ctx.PushThis(call.obj);
  ctx.PushQueueRefFrame();
  ctx.PushAssocRefFrame();
  // §20.17.2: the task is a calling context on the $stacktrace chain, as a
  // module task enabled by name is through PushTaskCallScope.
  ctx.PushFuncName(call.method->name);
  BindFunctionArgs(call.method, expr, ctx, arena);
  return true;
}

void TeardownInstanceTaskCall(const InstanceMethodInfo& call, const Expr* expr,
                              SimContext& ctx, Arena& arena) {
  // §13.5.2: output and inout arguments are copied back to the caller on
  // return, as the instance-method path does.
  WritebackOutputArgs(call.method, expr, ctx, arena);
  WritebackQueueRefs(ctx);
  WritebackAssocRefs(ctx);
  ctx.PopFuncName();
  if (call.obj != nullptr) ctx.PopThis();
  ctx.PopScope();
  ctx.PopMethodClass();
}

}  // namespace delta
