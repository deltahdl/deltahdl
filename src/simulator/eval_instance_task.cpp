// §13.3 with §8.6: a task enabled through an object handle, `h.t(...)`, may
// contain time-controlling statements, so it runs as a coroutine in
// ExecInstanceTaskCall (stmt_exec_class_task.cpp) rather than through the
// synchronous function interpreter ExecClassMethod drives. The frame such a
// call stands in is the one ExecInstanceMethodCall builds -- a scope, `this`,
// the queue and associative reference frames, the defining class as the
// enclosing scope (§8.15) -- and it is set up and torn down here, beside the
// resolution of the handle and the method, so the two callers agree on it.

#include "simulator/eval_instance_task.h"

#include "common/arena.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

namespace delta {

bool SetupInstanceTaskCall(const Expr* expr, SimContext& ctx, Arena& arena,
                           InstanceMethodInfo& call) {
  if (!expr || expr->kind != ExprKind::kCall) return false;
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  if (!ResolveInstanceMethod(parts, ctx, call)) return false;
  // §8.10: a static task has no `this` and is run in class scope by the
  // evaluator; only an instance task is enabled here.
  if (call.method->kind != ModuleItemKind::kTaskDecl || call.method->is_static)
    return false;
  ctx.PushMethodClass(call.owner);
  ctx.PushScope();
  ctx.PushThis(call.obj);
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
  ctx.PopThis();
  ctx.PopScope();
  ctx.PopMethodClass();
}

}  // namespace delta
