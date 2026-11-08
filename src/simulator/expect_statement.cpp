#include "common/arena.h"
#include "common/types.h"
#include "simulator/awaiters_event_control.h"
#include "simulator/exec_task.h"
#include "simulator/process.h"
#include "simulator/property_attempts.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_exec_assertion_internal.h"
#include "simulator/stmt_exec_internal.h"
#include "simulator/stmt_result.h"

namespace delta {

ExecTask ExecExpect(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  Process* proc = ctx.CurrentProcess();
  bool evaluated = proc != nullptr && stmt->is_concurrent_clocked &&
                   !stmt->assert_clock.empty();
  if (!evaluated) co_return StmtResult::kDone;
  proc->expect_decided = false;
  bool begun = false;
  while (!proc->expect_decided) {
    co_await EventAwaiter{ctx, stmt->assert_clock, arena};
    co_await RegionAwaiter{ctx, Region::kObserved};
    ExecConcurrentAssertionTick(
        stmt, begun ? AttemptInstances{} : AttemptInstances{nullptr}, ctx,
        arena);
    begun = true;
  }
  co_await RegionAwaiter{ctx, Region::kReactive};
  const Stmt* action =
      proc->expect_holds ? stmt->assert_pass_stmt : stmt->assert_fail_stmt;
  if (action != nullptr &&
      AssertionControlStatus(stmt, ctx).RunsAction(proc->expect_holds, false)) {
    co_return co_await ExecStmt(action, ctx, arena);
  }
  co_return StmtResult::kDone;
}

}  // namespace delta
