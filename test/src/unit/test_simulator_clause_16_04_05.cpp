#include <gtest/gtest.h>

#include <cstdint>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine.h"

using namespace delta;

namespace {

// §16.4.5 Deferred assertions and multiple processes.
//
// A deferred assertion is inherently associated with the process that executes
// it. A single deferred assertion textually contained in a function may be
// executed many times in one time step because several distinct processes call
// that function, and each of those executions is independent: failures,
// flushing, and reporting are tracked separately on each calling process's own
// deferred assertion report queue. The engine keys its pending reports by
// process id (SvaEngine::per_process_reports_), so the tests below drive that
// API with the same DeferredAssertion (modeling one function's assertion `a1`)
// queued under different process ids to observe the per-process independence.

struct MultiProcessFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
  SvaEngine engine;
};

// Models the §16.4.5 `fsm` example: function f's assertion a1 is called by both
// always_comb processes b1 and b2 in the same time step. Each call lands a
// report on its own process's queue, never on the other's.
TEST(DeferredMultipleProcesses, SameFunctionAssertionQueuesPerProcess) {
  MultiProcessFixture f;
  DeferredAssertion a1;
  a1.instance_name = "fsm.a1";
  a1.condition_val = 0;

  f.engine.QueuePendingReport("b1", a1, DeferralKind::kObserved);
  f.engine.QueuePendingReport("b2", a1, DeferralKind::kObserved);

  EXPECT_EQ(f.engine.GetDeferredReportQueue("b1").Size(), 1u);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("b2").Size(), 1u);
}

// Time step 1 of the example: a1 fails independently for processes b1 and b2,
// so its failure is reported twice. Both queues mature and yield their report
// independently.
TEST(DeferredMultipleProcesses, FailureInTwoProcessesIsReportedTwice) {
  MultiProcessFixture f;
  DeferredAssertion a1;
  a1.instance_name = "fsm.a1";
  a1.condition_val = 0;

  f.engine.QueuePendingReport("b1", a1, DeferralKind::kObserved);
  f.engine.QueuePendingReport("b2", a1, DeferralKind::kObserved);

  uint32_t executed = 0;
  f.engine.MatureObservedReports("b1");
  f.engine.MatureObservedReports("b2");
  executed += f.engine.ExecuteMaturedObservedInReactive("b1", f.scheduler,
                                                        f.ctx.CurrentTime());
  executed += f.engine.ExecuteMaturedObservedInReactive("b2", f.scheduler,
                                                        f.ctx.CurrentTime());

  EXPECT_EQ(executed, 2u);
}

// Time step 2 / 3 of the example: process b1 reaching a flush point clears only
// b1's pending report. A concurrent process b2 keeps its own pending report —
// the flush of one process is invisible to the other.
TEST(DeferredMultipleProcesses, FlushInOneProcessDoesNotAffectAnother) {
  MultiProcessFixture f;
  DeferredAssertion a1;
  a1.instance_name = "fsm.a1";
  a1.condition_val = 0;

  f.engine.QueuePendingReport("b1", a1, DeferralKind::kObserved);
  f.engine.QueuePendingReport("b2", a1, DeferralKind::kObserved);

  // b1's always_comb re-triggers (a flush point); b2 has not.
  f.engine.OnDeferredFlushPoint("b1", FlushPointReason::kAlwaysCombSignalDelta);

  EXPECT_EQ(f.engine.GetDeferredReportQueue("b1").Size(), 0u);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("b2").Size(), 1u);
}

// Maturation is also per process: confirming b1's reports for reporting does
// not mature b2's still-pending reports, which remain flushable.
TEST(DeferredMultipleProcesses, MaturingOneProcessLeavesOthersUnmatured) {
  MultiProcessFixture f;
  DeferredAssertion a1;
  a1.instance_name = "fsm.a1";
  a1.condition_val = 0;

  f.engine.QueuePendingReport("b1", a1, DeferralKind::kObserved);
  f.engine.QueuePendingReport("b2", a1, DeferralKind::kObserved);

  f.engine.MatureObservedReports("b1");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("b1").MaturedCount(), 1u);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("b2").MaturedCount(), 0u);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("b2").NonMaturedCount(), 1u);

  // b2 not having matured, its report is still subject to a later flush.
  f.engine.OnDeferredFlushPoint("b2", FlushPointReason::kAlwaysCombSignalDelta);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("b2").Size(), 0u);
}

// Time step 3 of the example: a1 fails in b1 (reported) while it passes in b2
// (no report queued at all). The processes contribute independently — a passing
// process leaves nothing on its queue while the failing process reports.
TEST(DeferredMultipleProcesses, PassingProcessQueuesNoReportWhileOtherReports) {
  MultiProcessFixture f;
  DeferredAssertion a1;
  a1.instance_name = "fsm.a1";
  a1.condition_val = 0;

  // Only the failing process b1 queues a report; the passing process b2 does
  // not enqueue anything.
  f.engine.QueuePendingReport("b1", a1, DeferralKind::kObserved);

  EXPECT_EQ(f.engine.GetDeferredReportQueue("b1").Size(), 1u);
  EXPECT_EQ(f.engine.PeekDeferredReportQueue("b2"), nullptr);
}

// The full three-process picture in a single time step: b1 is flushed (re-runs
// and passes), b3 also passes (no report), and b2 retains its failure report
// through maturation. Each process's outcome is independent of the others.
TEST(DeferredMultipleProcesses, ThreeProcessesResolveIndependently) {
  MultiProcessFixture f;
  DeferredAssertion a1;
  a1.instance_name = "fsm.a1";
  a1.condition_val = 0;

  f.engine.QueuePendingReport("b1", a1, DeferralKind::kObserved);
  f.engine.QueuePendingReport("b2", a1, DeferralKind::kObserved);

  // b1 hits a flush point; b2 matures; b3 never queued anything (it passed).
  f.engine.OnDeferredFlushPoint("b1", FlushPointReason::kEventControlResume);
  f.engine.MatureObservedReports("b2");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("b1").Size(), 0u);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("b2").MaturedCount(), 1u);
  EXPECT_EQ(f.engine.PeekDeferredReportQueue("b3"), nullptr);

  // b2's matured report executes; b1's was flushed so nothing executes there.
  uint32_t b1_exec = f.engine.ExecuteMaturedObservedInReactive(
      "b1", f.scheduler, f.ctx.CurrentTime());
  uint32_t b2_exec = f.engine.ExecuteMaturedObservedInReactive(
      "b2", f.scheduler, f.ctx.CurrentTime());
  EXPECT_EQ(b1_exec, 0u);
  EXPECT_EQ(b2_exec, 1u);
}

// Per-process independence holds for final deferred assertions too, not just
// observed ones: when a function's `assert final` fails in two processes, each
// process's report matures and executes in the Postponed region on its own
// queue, so the failure is reported once per process.
TEST(DeferredMultipleProcesses, FinalDeferredFailureInTwoProcessesReportedTwice) {
  MultiProcessFixture f;
  DeferredAssertion a1;
  a1.instance_name = "fsm.a1";
  a1.condition_val = 0;

  f.engine.QueuePendingReport("b1", a1, DeferralKind::kFinal);
  f.engine.QueuePendingReport("b2", a1, DeferralKind::kFinal);

  uint32_t executed = 0;
  f.engine.MatureFinalReports("b1");
  f.engine.MatureFinalReports("b2");
  executed += f.engine.ExecuteMaturedFinalInPostponed("b1", f.scheduler,
                                                      f.ctx.CurrentTime());
  executed += f.engine.ExecuteMaturedFinalInPostponed("b2", f.scheduler,
                                                      f.ctx.CurrentTime());

  EXPECT_EQ(executed, 2u);
}

// Final deferred maturation and flushing are also scoped per process: maturing
// b1's final report does not mature b2's, and a flush point reached by b2
// clears only b2's still-pending final report — b1's report is untouched and
// still executes in the Postponed region.
TEST(DeferredMultipleProcesses, FinalDeferredMaturationAndFlushArePerProcess) {
  MultiProcessFixture f;
  DeferredAssertion a1;
  a1.instance_name = "fsm.a1";
  a1.condition_val = 0;

  f.engine.QueuePendingReport("b1", a1, DeferralKind::kFinal);
  f.engine.QueuePendingReport("b2", a1, DeferralKind::kFinal);

  f.engine.MatureFinalReports("b1");
  EXPECT_EQ(f.engine.GetDeferredReportQueue("b1").MaturedCount(), 1u);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("b2").MaturedCount(), 0u);

  // b2 reaches a flush point; only its non-matured final report is cleared.
  f.engine.OnDeferredFlushPoint("b2", FlushPointReason::kWaitResume);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("b2").Size(), 0u);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("b1").Size(), 1u);

  uint32_t b1_exec = f.engine.ExecuteMaturedFinalInPostponed(
      "b1", f.scheduler, f.ctx.CurrentTime());
  uint32_t b2_exec = f.engine.ExecuteMaturedFinalInPostponed(
      "b2", f.scheduler, f.ctx.CurrentTime());
  EXPECT_EQ(b1_exec, 1u);
  EXPECT_EQ(b2_exec, 0u);
}

}  // namespace
