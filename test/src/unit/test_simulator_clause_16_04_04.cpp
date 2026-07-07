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

using namespace delta;

namespace {

struct DeferredDisableFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
  SvaEngine engine;

  void QueueObserved(std::string_view process_id, std::string_view instance) {
    DeferredAssertion da;
    da.condition_val = 0;
    da.instance_name = std::string(instance);
    engine.QueuePendingReport(process_id, da, DeferralKind::kObserved);
  }
};

// §16.4.4: disabling a specific deferred assertion, or the outermost scope of a
// procedure with an active deferred report queue, clears pending reports;
// disabling a task or a non-outermost scope does not. The classification
// predicate is observed through the queue-flush tests below: each apply call
// clears (or preserves) the queue only when the predicate accepts (or rejects)
// its disable target.

// §16.4.4 Claim A: disabling a specific deferred assertion cancels the pending
// reports for that assertion only, leaving other assertions' reports queued.
TEST(DeferredDisableSpecific, CancelsOnlyNamedAssertionPendingReports) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.QueueObserved("p0", "a2");
  ASSERT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 2u);

  f.engine.ApplyDisableToDeferredAssertions(
      "p0", DisableTarget::kSpecificAssertion, "a1");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 1u);
  EXPECT_EQ(
      f.engine.GetDeferredReportQueue("p0").Entries().front().da.instance_name,
      "a2");
}

// §16.4.4 Claim A: a report that already matured is no longer pending, so
// disabling its assertion does not remove it.
TEST(DeferredDisableSpecific, LeavesMaturedReportOfNamedAssertion) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.engine.MatureObservedReports("p0");
  ASSERT_EQ(f.engine.GetDeferredReportQueue("p0").MaturedCount(), 1u);

  f.engine.ApplyDisableToDeferredAssertions(
      "p0", DisableTarget::kSpecificAssertion, "a1");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 1u);
}

// §16.4.4 Claim B: disabling the outermost scope flushes the whole pending
// report queue of the process.
TEST(DeferredDisableOutermost, FlushesAllPendingReports) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.QueueObserved("p0", "a2");
  ASSERT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 2u);

  f.engine.ApplyDisableToDeferredAssertions("p0",
                                            DisableTarget::kOutermostScope, "");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 0u);
}

// §16.4.4 Claim B: only pending (non-matured) reports are cleared; a matured
// report survives an outermost-scope disable.
TEST(DeferredDisableOutermost, LeavesMaturedReports) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.engine.MatureObservedReports("p0");
  f.QueueObserved("p0", "a2");
  ASSERT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 2u);

  f.engine.ApplyDisableToDeferredAssertions("p0",
                                            DisableTarget::kOutermostScope, "");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 1u);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").MaturedCount(), 1u);
}

// §16.4.4 Claim C: disabling a task does not flush any pending reports.
TEST(DeferredDisableNoFlush, TaskLeavesQueueIntact) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.QueueObserved("p0", "a2");

  f.engine.ApplyDisableToDeferredAssertions("p0", DisableTarget::kTask, "a1");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 2u);
}

// §16.4.4 Claim C: disabling a non-outermost scope does not flush any pending
// reports.
TEST(DeferredDisableNoFlush, NonOutermostScopeLeavesQueueIntact) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.QueueObserved("p0", "a2");

  f.engine.ApplyDisableToDeferredAssertions(
      "p0", DisableTarget::kNonOutermostScope, "");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 2u);
}

// §16.4.4 Claim A, edge case: naming an assertion that has no pending reports
// leaves the queue untouched.
TEST(DeferredDisableSpecific, UnknownAssertionNameLeavesQueueIntact) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.QueueObserved("p0", "a2");

  f.engine.ApplyDisableToDeferredAssertions(
      "p0", DisableTarget::kSpecificAssertion, "missing");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 2u);
}

// §16.4.4 Claim A, edge case: every pending report of the named assertion is
// cancelled, even when the same assertion queued several reports.
TEST(DeferredDisableSpecific, CancelsAllPendingReportsOfSameAssertion) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.QueueObserved("p0", "a1");
  f.QueueObserved("p0", "a2");
  ASSERT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 3u);

  f.engine.ApplyDisableToDeferredAssertions(
      "p0", DisableTarget::kSpecificAssertion, "a1");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 1u);
  EXPECT_EQ(
      f.engine.GetDeferredReportQueue("p0").Entries().front().da.instance_name,
      "a2");
}

// §16.4.4 Claim A, edge case: deferred reports are per process, so disabling a
// specific assertion in one process does not touch another process's queue.
TEST(DeferredDisableSpecific, DoesNotAffectOtherProcessQueue) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.QueueObserved("p1", "a1");

  f.engine.ApplyDisableToDeferredAssertions(
      "p0", DisableTarget::kSpecificAssertion, "a1");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 0u);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("p1").Size(), 1u);
}

// §16.4.4 Claim B, edge case: an outermost-scope disable on a process with no
// pending reports is a safe no-op.
TEST(DeferredDisableOutermost, EmptyQueueIsSafeNoOp) {
  DeferredDisableFixture f;

  f.engine.ApplyDisableToDeferredAssertions("p0",
                                            DisableTarget::kOutermostScope, "");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 0u);
}

// §16.4.4 Claim B, edge case: when every report has already matured, an
// outermost-scope disable clears nothing.
TEST(DeferredDisableOutermost, AllMaturedQueueSurvives) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.QueueObserved("p0", "a2");
  f.engine.MatureObservedReports("p0");
  ASSERT_EQ(f.engine.GetDeferredReportQueue("p0").MaturedCount(), 2u);

  f.engine.ApplyDisableToDeferredAssertions("p0",
                                            DisableTarget::kOutermostScope, "");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 2u);
}

// §16.4.4 Claim B, edge case: an outermost-scope disable of one process leaves
// another process's pending reports in place.
TEST(DeferredDisableOutermost, DoesNotAffectOtherProcessQueue) {
  DeferredDisableFixture f;
  f.QueueObserved("p0", "a1");
  f.QueueObserved("p1", "a1");

  f.engine.ApplyDisableToDeferredAssertions("p0",
                                            DisableTarget::kOutermostScope, "");

  EXPECT_EQ(f.engine.GetDeferredReportQueue("p0").Size(), 0u);
  EXPECT_EQ(f.engine.GetDeferredReportQueue("p1").Size(), 1u);
}

// --- Real-source tests: the disable rule on the live deferred-report path ---
//
// The synthetic tests above exercise the classification model. These drive real
// SystemVerilog through parse/elaborate/lower/run so the disable statement's
// interaction with the actual deferred immediate assertion machinery
// (ExecDisableImpl clearing a pending report queued by `assert #0`, gated on
// the process's deferred report generation from §16.4.2) is observed end to
// end. The deferred assertions are built on their dependency constructs: an
// event-control procedure (§9.6.2 disable target), a named begin-end block, and
// a task.

// §16.4.4 Claim B (outermost scope): a process (b3) that disables another
// procedure's outermost scope (b2) flushes b2's pending deferred report. The
// `#1` lets both `always` blocks arm their event controls first; then b2 is
// triggered and its failing `assert #0 (0)` queues a report, and the `#0`
// re-schedules the initial into the same time step's inactive set so b3 is then
// triggered and runs `disable b2` before the Reactive region. The pending
// report is flushed, so its else action never runs and flag stays 0.
TEST(DisableOutermostScopeLive,
     CrossProcessDisableFlushesQueuedDeferredReport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a = 0;\n"
      "  logic clear = 0;\n"
      "  int flag = 0;\n"
      "  always @(a) begin : b2\n"
      "    assert #0 (0) else flag = 1;\n"
      "  end\n"
      "  always @(clear) begin : b3\n"
      "    disable b2;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 a = 1'b1;\n"
      "    #0 clear = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* flag = f.ctx.FindVariable("flag");
  ASSERT_NE(flag, nullptr);
  EXPECT_EQ(flag->value.ToUint64(), 0u);
}

// §16.4.4 Claim B (whole queue): an outermost-scope disable flushes the entire
// pending report queue of the process, not just one report -- the property that
// distinguishes it from the specific-assertion disable of Claim A. Here b2
// queues two pending reports in one activation; the single `disable b2` from b3
// clears both, so neither else action runs and flag1 and flag2 both stay 0.
TEST(DisableOutermostScopeLive, DisableFlushesEveryPendingReportOfProcess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a = 0;\n"
      "  logic clear = 0;\n"
      "  int flag1 = 0;\n"
      "  int flag2 = 0;\n"
      "  always @(a) begin : b2\n"
      "    assert #0 (0) else flag1 = 1;\n"
      "    assert #0 (0) else flag2 = 1;\n"
      "  end\n"
      "  always @(clear) begin : b3\n"
      "    disable b2;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 a = 1'b1;\n"
      "    #0 clear = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* flag1 = f.ctx.FindVariable("flag1");
  ASSERT_NE(flag1, nullptr);
  EXPECT_EQ(flag1->value.ToUint64(), 0u);
  auto* flag2 = f.ctx.FindVariable("flag2");
  ASSERT_NE(flag2, nullptr);
  EXPECT_EQ(flag2->value.ToUint64(), 0u);
}

// §16.4.4 Claim B (contrast): with no disabling process, the same deferred
// report reaches no flush point between being queued and its Reactive region,
// so it matures and its else action runs, setting flag to 1. This confirms the
// disable -- not a dropped report -- is what suppresses the report above.
TEST(DisableOutermostScopeLive, WithoutDisableDeferredReportExecutes) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a = 0;\n"
      "  int flag = 0;\n"
      "  always @(a) begin : b2\n"
      "    assert #0 (0) else flag = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 a = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* flag = f.ctx.FindVariable("flag");
  ASSERT_NE(flag, nullptr);
  EXPECT_EQ(flag->value.ToUint64(), 1u);
}

// §16.4.4 Claim C (non-outermost scope): disabling a non-outermost named block
// does not flush pending reports. The initial queues a report inside block
// `inner`, then `disable inner` unwinds out of that block (the process
// continues, running x = 7). No flush occurs, so the report matures and its
// else action sets flag to 1; x == 7 confirms the process continued past the
// block.
TEST(DisableNonOutermostScopeLive,
     InnerBlockDisableDoesNotFlushDeferredReport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int flag = 0;\n"
      "  logic [7:0] x = 0;\n"
      "  initial begin\n"
      "    begin : inner\n"
      "      assert #0 (0) else flag = 1;\n"
      "      disable inner;\n"
      "    end\n"
      "    x = 8'd7;\n"
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
  EXPECT_EQ(x->value.ToUint64(), 7u);
}

// §16.4.4 Claim C (task): disabling a task does not flush pending reports. The
// task queues a report and then `disable do_check` returns from the task; the
// calling process continues (running x = 5). No flush occurs, so the report
// matures and sets flag to 1.
TEST(DisableNonOutermostScopeLive, TaskDisableDoesNotFlushDeferredReport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int flag = 0;\n"
      "  logic [7:0] x = 0;\n"
      "  task do_check;\n"
      "    begin\n"
      "      assert #0 (0) else flag = 1;\n"
      "      disable do_check;\n"
      "    end\n"
      "  endtask\n"
      "  initial begin\n"
      "    do_check;\n"
      "    x = 8'd5;\n"
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
  EXPECT_EQ(x->value.ToUint64(), 5u);
}

// §16.4.4 Claim B (report-kind input form -- final deferred): the
// outermost-scope disable flushes a final deferred assertion's report as well
// as an observed
// (#0) one. A final report is pending until the Postponed region; b2 queues it
// on its (a==1) activation and b3's `disable b2` runs first (Active/inactive of
// the same time step), so the report is flushed before the Postponed region and
// its else action never runs -- flag stays 0. This exercises the
// Postponed-region guard, a distinct path from the Reactive-region observed
// reports above.
TEST(DisableOutermostScopeLive, DisableFlushesFinalDeferredReport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a = 0;\n"
      "  logic clear = 0;\n"
      "  int flag = 0;\n"
      "  always @(a) begin : b2\n"
      "    assert final (0) else flag = 1;\n"
      "  end\n"
      "  always @(clear) begin : b3\n"
      "    disable b2;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 a = 1'b1;\n"
      "    #0 clear = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* flag = f.ctx.FindVariable("flag");
  ASSERT_NE(flag, nullptr);
  EXPECT_EQ(flag->value.ToUint64(), 0u);
}

// §16.4.4 Claim B (report-path input form -- default $error): a failing
// deferred assertion with no else clause queues its implicit $error as a
// pending report (a different production path from an else action). The
// outermost-scope disable flushes it too: b2 queues the default report on its
// (a==1) activation, b3 disables b2 before the Reactive region, so no severity
// is ever emitted.
TEST(DisableOutermostScopeLive, DisableFlushesDefaultErrorReport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a = 0;\n"
      "  logic clear = 0;\n"
      "  always @(a) begin : b2\n"
      "    assert #0 (0);\n"
      "  end\n"
      "  always @(clear) begin : b3\n"
      "    disable b2;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 a = 1'b1;\n"
      "    #0 clear = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverity(), "");
}

// §16.4.4 Claim C (report-kind input form -- final deferred): disabling a
// non-outermost scope does not flush a final deferred report either. The
// initial queues a final report inside block `inner`, then `disable inner`
// unwinds out of the block (the process continues, running x = 7). No flush
// occurs, so the report matures in the Postponed region and sets flag to 1.
TEST(DisableNonOutermostScopeLive, InnerBlockDisableDoesNotFlushFinalReport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int flag = 0;\n"
      "  logic [7:0] x = 0;\n"
      "  initial begin\n"
      "    begin : inner\n"
      "      assert final (0) else flag = 1;\n"
      "      disable inner;\n"
      "    end\n"
      "    x = 8'd7;\n"
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
  EXPECT_EQ(x->value.ToUint64(), 7u);
}

// §16.4.4 Claim A (specific-assertion disable): `disable <assertion_label>`
// cancels that assertion's still-pending report and lets the process keep
// running (it does not unwind, unlike disabling a scope). Here `a1: assert #0`
// fails and queues its else action; `disable a1` cancels it before the Reactive
// region, so flag stays 0, and x = 9 confirms the process continued past the
// disable.
TEST(DisableSpecificAssertionLive, CancelsItsPendingReportAndProcessContinues) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int flag = 0;\n"
      "  logic [7:0] x = 0;\n"
      "  initial begin\n"
      "    a1: assert #0 (0) else flag = 1;\n"
      "    disable a1;\n"
      "    x = 8'd9;\n"
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
  EXPECT_EQ(x->value.ToUint64(), 9u);
}

// §16.4.4 Claim A (specificity): a specific-assertion disable cancels only the
// named assertion's reports, leaving other assertions' pending reports queued.
// Both a1 and a2 fail and queue reports; `disable a1` cancels a1's report only,
// so flag1 stays 0 while a2's report matures and sets flag2 to 1.
TEST(DisableSpecificAssertionLive, LeavesOtherAssertionsPendingReports) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int flag1 = 0;\n"
      "  int flag2 = 0;\n"
      "  initial begin\n"
      "    a1: assert #0 (0) else flag1 = 1;\n"
      "    a2: assert #0 (0) else flag2 = 1;\n"
      "    disable a1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* flag1 = f.ctx.FindVariable("flag1");
  ASSERT_NE(flag1, nullptr);
  EXPECT_EQ(flag1->value.ToUint64(), 0u);
  auto* flag2 = f.ctx.FindVariable("flag2");
  ASSERT_NE(flag2, nullptr);
  EXPECT_EQ(flag2->value.ToUint64(), 1u);
}

}  // namespace
