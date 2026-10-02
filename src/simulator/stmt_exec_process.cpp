// §9.7's process-control calls that suspend the process making them: `await()`
// on another process, which waits for it to end, and `suspend()` on the
// process itself, which stops it before the call returns.

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

// §9.7: the process shall be suspended before suspend() returns, so a process
// suspending itself parks here, its continuation stashed where resume()
// replays it (DriveResumedProcess in eval_process_methods.cpp).
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

// The process a `<handle>.await()` call targets, validated: null, with the
// diagnostic, where the call names none a process may legally await. The
// handle is any ResolveProcessMethodCall reads: `p`, `p::proc` (§26.3), or an
// element of an array of them, `job[k]` (§9.7).
static Process* ResolveProcessAwaitTarget(const Expr* expr, Process* proc,
                                          SimContext& ctx) {
  if (!proc) return nullptr;
  if (proc->kind == ProcessKind::kFinal ||
      proc->kind == ProcessKind::kContAssign) {
    ctx.GetDiag().Error(
        expr->range.start,
        "await() shall only target a process created by an initial "
        "procedure, always procedure, or fork block",
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
  // suspend() on the running process: the call records the suspension and
  // reports what §9.7 forbids, and the process then stops here.
  Logic4Vec ignored;
  TryEvalProcessMethodCall(expr, ctx, arena, ignored);
  held.Release();
  co_await SelfSuspendAwaiter{call.proc};
  co_return StmtResult::kDone;
}

}  // namespace delta
