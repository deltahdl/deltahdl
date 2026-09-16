#include <cstdint>

#include "common/arena.h"
#include "parser/ast.h"
#include "simulator/awaiters_event_control.h"
#include "simulator/process.h"
#include "simulator/property_attempts.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_exec_assertion_internal.h"
#include "simulator/stmt_exec_internal.h"
#include "simulator/sva_engine_queues.h"

namespace delta {

// §16.17: the expect statement starts a single thread of evaluation of its
// property on the subsequent clocking event, the first evaluation taking
// place at the next tick and not at one the process has already seen, and
// the process blocks until the property succeeds or fails, its attempt
// advanced in the Observed region of each tick in the process itself, as
// §16.5 evaluates a concurrent assertion; no further evaluation begins
// until the statement is executed again. The verdict, written by the
// attempt's conclusion, unblocks the process in the Reactive region, where
// it executes the pass statement or the else clause, a failure with no
// else clause having been reported through $error where it was concluded
// (§20.11 having $assertcontrol able to suppress that). A statement whose
// spec this tool does not evaluate, or whose checking $assertcontrol has
// turned off, blocks nothing.
ExecTask ExecExpect(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  Process* proc = ctx.CurrentProcess();
  bool evaluated = proc != nullptr && stmt->is_concurrent_clocked &&
                   !stmt->assert_clock.empty() &&
                   ctx.AssertCheckingEnabled(
                       static_cast<uint32_t>(AssertionTypeBit::kExpect),
                       static_cast<uint32_t>(DirectiveTypeBit::kAssert));
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
  if (action != nullptr) co_return co_await ExecStmt(action, ctx, arena);
  co_return StmtResult::kDone;
}

}  // namespace delta
