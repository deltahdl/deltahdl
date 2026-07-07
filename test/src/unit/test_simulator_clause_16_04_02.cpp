#include <gtest/gtest.h>

#include <cstdint>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine.h"

// §16.4.2 "Deferred assertion flush points" defines when a process reaches a
// deferred assertion flush point: (1) it resumes after suspending on an event
// control or wait; (2) an always_comb/always_latch procedure re-runs because a
// dependent signal changed; (3) its outermost scope is disabled (see §16.4.4).
// Reaching such a point clears the process's still-pending (not-yet-matured)
// deferred immediate assertion reports.
//
// The first group of tests exercises the classification predicate and the
// queue-flush helper directly. The second group drives real SystemVerilog
// through parse/elaborate/lower/run and observes the live path (stmt_exec.cpp
// scheduling a deferred report, and the flush at each resume/re-trigger site)
// clearing -- or, once matured, keeping -- a report queued by a real
// `assert #0` built on the dependency constructs (event control, wait,
// always_comb).

using namespace delta;

namespace {

struct FlushPointFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
  SvaEngine engine;
};

// The classification predicate IsDeferredFlushPoint(reason) is exercised
// through the queue-flush tests below: OnDeferredFlushPoint clears the pending
// reports only when the predicate accepts the reason, so each reason's
// true/false classification is observed together with its flushing effect.

TEST(DeferredFlushPoints, EventResumeClearsNonMaturedQueue) {
  FlushPointFixture f;
  DeferredAssertion da;
  da.condition_val = 1;
  f.engine.QueuePendingReport("p0", da, DeferralKind::kObserved);
  f.engine.QueuePendingReport("p0", da, DeferralKind::kObserved);

  f.engine.OnDeferredFlushPoint("p0", FlushPointReason::kEventControlResume);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 0u);
}

TEST(DeferredFlushPoints, WaitResumeClearsNonMaturedQueue) {
  FlushPointFixture f;
  DeferredAssertion da;
  da.condition_val = 0;
  f.engine.QueuePendingReport("p0", da, DeferralKind::kObserved);

  f.engine.OnDeferredFlushPoint("p0", FlushPointReason::kWaitResume);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 0u);
}

TEST(DeferredFlushPoints, AlwaysCombSignalDeltaClearsNonMaturedQueue) {
  FlushPointFixture f;
  DeferredAssertion da;
  da.condition_val = 0;
  f.engine.QueuePendingReport("alc", da, DeferralKind::kObserved);

  f.engine.OnDeferredFlushPoint("alc",
                                FlushPointReason::kAlwaysCombSignalDelta);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("alc").Size(), 0u);
}

TEST(DeferredFlushPoints, AlwaysLatchSignalDeltaClearsNonMaturedQueue) {
  FlushPointFixture f;
  DeferredAssertion da;
  da.condition_val = 1;
  f.engine.QueuePendingReport("alt", da, DeferralKind::kObserved);

  f.engine.OnDeferredFlushPoint("alt",
                                FlushPointReason::kAlwaysLatchSignalDelta);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("alt").Size(), 0u);
}

TEST(DeferredFlushPoints, DisableOuterScopeClearsNonMaturedQueue) {
  FlushPointFixture f;
  DeferredAssertion da;
  da.condition_val = 1;
  f.engine.QueuePendingReport("p0", da, DeferralKind::kObserved);

  f.engine.OnDeferredFlushPoint("p0", FlushPointReason::kDisableOuterScope);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 0u);
}

TEST(DeferredFlushPoints, NoneReasonDoesNotClearQueue) {
  FlushPointFixture f;
  DeferredAssertion da;
  da.condition_val = 1;
  f.engine.QueuePendingReport("p0", da, DeferralKind::kObserved);

  f.engine.OnDeferredFlushPoint("p0", FlushPointReason::kNone);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 1u);
}

TEST(DeferredFlushPoints, FlushOnEmptyQueueIsSafeNoOp) {
  FlushPointFixture f;
  f.engine.OnDeferredFlushPoint("nonexistent",
                                FlushPointReason::kDisableOuterScope);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("nonexistent").Size(), 0u);
}

// --- Real-source tests: the live deferred-report path and its flush points ---

// §16.4.2 (bullet 2): an always_comb procedure that queues a deferred report
// and is then re-run by a dependent-signal transition in the same time step
// reaches a flush point on resume. Here the first evaluation sees a==1 && b==1
// so `assert #0 (!(a && b))` fails and its else action (flag=1) is queued as a
// pending report. The nonblocking update `b <= 0` re-triggers the procedure
// within the time step; on resume the pending report is flushed before its
// Reactive region runs, and the re-evaluation (a==1, b==0) passes, so nothing
// executes and flag stays 0. Without the flush the stale report would run and
// set flag to 1.
TEST(DeferredFlushPointsLive, AlwaysCombRetriggerFlushesDeferredReport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b;\n"
      "  logic [7:0] z;\n"
      "  int flag = 0;\n"
      "  always_comb begin\n"
      "    if (a) z = 8'd1;\n"
      "    else if (b) z = 8'd2;\n"
      "    else z = 8'd0;\n"
      "    assert #0 (!(a && b)) else flag = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    a = 1'b1;\n"
      "    b = 1'b1;\n"
      "    b <= 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("flag");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// §16.4.2 (bullet 2, always_latch): the flush point applies to always_latch
// procedures as well as always_comb -- both resume on a dependent-signal
// transition. The first evaluation sees en==1 so `assert #0 (!en)` fails and
// queues its else action; the nonblocking `en <= 0` re-triggers the procedure
// in the same time step, flushing the pending report before its Reactive
// region, and the re-evaluation (en==0) passes, so flag stays 0.
TEST(DeferredFlushPointsLive, AlwaysLatchRetriggerFlushesDeferredReport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en, d;\n"
      "  logic [7:0] q;\n"
      "  int flag = 0;\n"
      "  always_latch begin\n"
      "    if (en) q = d;\n"
      "    assert #0 (!en) else flag = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    d = 1'b1;\n"
      "    en = 1'b1;\n"
      "    en <= 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("flag");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// §16.4.2 (contrast to the above): when the always_comb settles without a
// re-triggering transition, no flush point intervenes between queuing the
// report and its Reactive region, so the deferred report is executed. The block
// evaluates once with a==0, `assert #0 (a)` fails, and its else action runs in
// the Reactive region, setting flag to 1. This confirms the flush -- not a
// dropped report path -- is what suppresses the report in the re-trigger case.
TEST(DeferredFlushPointsLive, SettledAlwaysCombDeferredReportExecutes) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a;\n"
      "  logic [7:0] z;\n"
      "  int flag = 0;\n"
      "  always_comb begin\n"
      "    if (a) z = 8'd1;\n"
      "    else z = 8'd0;\n"
      "    assert #0 (a) else flag = 1;\n"
      "  end\n"
      "  initial a = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("flag");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §16.4.2 (bullet 1, event control): a process that queues a deferred report
// and then suspends on an event control reaches a flush point when it resumes
// in the same time step. The other initial triggers `e` at time 0, so the
// process resumes before the Reactive region, the report queued by the failing
// `assert #0 (0)` is flushed, and flag stays 0.
TEST(DeferredFlushPointsLive, EventControlResumeFlushesDeferredReport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event e;\n"
      "  int flag = 0;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    assert #0 (0) else flag = 1;\n"
      "    @e;\n"
      "    x = 8'd3;\n"
      "  end\n"
      "  initial begin\n"
      "    -> e;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* flag = f.ctx.FindVariable("flag");
  ASSERT_NE(flag, nullptr);
  EXPECT_EQ(flag->value.ToUint64(), 0u);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 3u);
}

// §16.4.2 (maturation boundary): a report matures at the end of the time step
// in which it was queued and can no longer be flushed. Here the report is
// queued at time 0 and executes in the Reactive region of time 0 (setting flag
// to 1); the process only resumes from `@e` at time 1, so the flush on that
// later resume finds nothing to clear and the already-executed report stands.
TEST(DeferredFlushPointsLive, MaturedDeferredReportSurvivesLaterEventResume) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event e;\n"
      "  int flag = 0;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    assert #0 (0) else flag = 1;\n"
      "    @e;\n"
      "    x = 8'd3;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 -> e;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* flag = f.ctx.FindVariable("flag");
  ASSERT_NE(flag, nullptr);
  EXPECT_EQ(flag->value.ToUint64(), 1u);
}

// §16.4.2 (bullet 1, wait): resuming after suspending on a wait statement is
// likewise a flush point. The report queued by the failing `assert #0 (0)` is
// flushed when `wait (ready)` resumes at time 0 (the other initial drives
// ready high), so flag stays 0.
TEST(DeferredFlushPointsLive, WaitResumeFlushesDeferredReport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic ready;\n"
      "  int flag = 0;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    ready = 1'b0;\n"
      "    assert #0 (0) else flag = 1;\n"
      "    wait (ready);\n"
      "    x = 8'd3;\n"
      "  end\n"
      "  initial begin\n"
      "    ready = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* flag = f.ctx.FindVariable("flag");
  ASSERT_NE(flag, nullptr);
  EXPECT_EQ(flag->value.ToUint64(), 0u);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 3u);
}

// §16.4.2 (default $error is also a pending report): the flush applies to the
// implicit $error a failing deferred assert emits when it has no else clause.
// The always_comb queues the default report on its first (a==1,b==1)
// evaluation; the `b <= 0` re-trigger flushes it before the Reactive region, so
// no severity is ever emitted.
TEST(DeferredFlushPointsLive, AlwaysCombRetriggerFlushesDefaultErrorReport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b;\n"
      "  logic [7:0] z;\n"
      "  always_comb begin\n"
      "    if (a) z = 8'd1;\n"
      "    else if (b) z = 8'd2;\n"
      "    else z = 8'd0;\n"
      "    assert #0 (!(a && b));\n"
      "  end\n"
      "  initial begin\n"
      "    a = 1'b1;\n"
      "    b = 1'b1;\n"
      "    b <= 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverity(), "");
}

// §16.4.2 (report-kind input form -- final deferred): a final deferred
// assertion's report is pending until the Postponed region, so it too is
// flushed when the process reaches a flush point first. The always_comb queues
// the final report on its (a==1,b==1) evaluation; the `b <= 0` re-trigger
// flushes it before the Postponed region and the re-evaluation passes, so the
// else action never runs and flag stays 0. This exercises the Postponed-region
// guard, distinct from the Reactive-region path taken by observed (#0) reports.
TEST(DeferredFlushPointsLive, AlwaysCombRetriggerFlushesFinalDeferredReport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b;\n"
      "  logic [7:0] z;\n"
      "  int flag = 0;\n"
      "  always_comb begin\n"
      "    if (a) z = 8'd1;\n"
      "    else if (b) z = 8'd2;\n"
      "    else z = 8'd0;\n"
      "    assert final (!(a && b)) else flag = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    a = 1'b1;\n"
      "    b = 1'b1;\n"
      "    b <= 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("flag");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// §16.4.2 (negative form): a flush point on a wait is reached only when the
// process actually suspends. A `wait` whose condition already holds does not
// suspend, so it is not a flush point; the report queued by the failing
// `assert #0 (0)` is not cleared and executes in the Reactive region, setting
// flag to 1 (and the following x=3 still runs, confirming no suspension).
TEST(DeferredFlushPointsLive, WaitAlreadyTrueDoesNotFlushDeferredReport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int flag = 0;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    assert #0 (0) else flag = 1;\n"
      "    wait (1'b1);\n"
      "    x = 8'd3;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* flag = f.ctx.FindVariable("flag");
  ASSERT_NE(flag, nullptr);
  EXPECT_EQ(flag->value.ToUint64(), 1u);
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 3u);
}

// §16.4.2 (per-process scope): a flush point is a property of the process that
// reaches it -- only that process's pending reports are cleared. Process pA
// queues a report and then resumes from `@e` in the same time step (a flush
// point), so its report is flushed and flag_a stays 0. Process pB queues its
// own report but never reaches a flush point, so pB's report matures and runs,
// setting flag_b to 1. This confirms pA's flush does not reach pB's queue.
TEST(DeferredFlushPointsLive, PerProcessFlushDoesNotClearOtherProcessReport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event e;\n"
      "  int flag_a = 0;\n"
      "  int flag_b = 0;\n"
      "  initial begin\n"
      "    assert #0 (0) else flag_a = 1;\n"
      "    @e;\n"
      "  end\n"
      "  initial begin\n"
      "    assert #0 (0) else flag_b = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    -> e;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* flag_a = f.ctx.FindVariable("flag_a");
  ASSERT_NE(flag_a, nullptr);
  EXPECT_EQ(flag_a->value.ToUint64(), 0u);
  auto* flag_b = f.ctx.FindVariable("flag_b");
  ASSERT_NE(flag_b, nullptr);
  EXPECT_EQ(flag_b->value.ToUint64(), 1u);
}

}  // namespace
