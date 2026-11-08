#include <coroutine>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/awaiters.h"
#include "simulator/eval_call_result.h"
#include "simulator/eval_function_internal.h"
#include "simulator/exec_task.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"
#include "simulator/stmt_exec_internal.h"
#include "simulator/stmt_result.h"

namespace delta {

namespace {

struct SelfSuspendAwaiter {
  Process* proc;

  bool await_ready() const noexcept {
    return proc == nullptr || !proc->is_suspended;
  }
  void await_suspend(std::coroutine_handle<> h) const {
    proc->pending_wake = h;
  }
  void await_resume() const noexcept {}
};

}  // namespace

static Process* ResolveProcessAwaitTarget(const Expr* expr, Process* proc,
                                          SimContext& ctx) {
  if (!proc) return nullptr;
  if (proc->kind == ProcessKind::kFinal ||
      proc->kind == ProcessKind::kContAssign) {
    ctx.GetDiag().Error(
        expr->range.start,
        "await() acts only on a process begun by an initial or always "
        "procedure or by a fork block within one",
        Subclause("9.7"));
    return nullptr;
  }
  if (proc == ctx.CurrentProcess()) {
    ctx.GetDiag().Error(expr->range.start,
                        "process cannot await its own termination",
                        Subclause("9.7"));
    return nullptr;
  }
  return proc;
}

bool IsSuspendingProcessCall(const Expr* expr, SimContext& ctx, Arena& arena) {
  ProcessMethodCall call;
  if (!ResolveProcessMethodCall(expr, ctx, arena, call)) return false;
  return call.method == "await" ||
         (call.method == "suspend" && call.proc != nullptr &&
          call.proc == ctx.CurrentProcess());
}

ExecTask ExecSuspendingProcessCall(const Expr* expr, SimContext& ctx,
                                   Arena& arena,
                                   CallResultReceiverScope& held) {
  ProcessMethodCall call;
  ResolveProcessMethodCall(expr, ctx, arena, call);
  if (call.method == "await") {
    Process* target = ResolveProcessAwaitTarget(expr, call.proc, ctx);
    held.Release();
    if (target) co_await ProcessAwaitAwaiter{target};
    co_return StmtResult::kDone;
  }
  Logic4Vec ignored;
  TryEvalProcessMethodCall(expr, ctx, arena, ignored);
  held.Release();
  co_await SelfSuspendAwaiter{call.proc};
  co_return StmtResult::kDone;
}

}  // namespace delta
