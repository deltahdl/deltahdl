#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"

// §16.4.1 "Deferred assertion reporting" governs the runtime handling of a
// deferred immediate assertion's report: when the assertion passes or fails the
// action block (or the default $error, when an assert/assume fails with no else
// clause) is not executed where the assertion is processed. It becomes a
// pending report and is executed later in the current time step -- in the
// Reactive region for an observed (#0) deferred assertion and in the Postponed
// region for a final deferred assertion. These tests drive real SystemVerilog
// source through parse/elaborate/lower/run and observe the live simulator path
// (stmt_exec.cpp) applying that rule, rather than poking an intermediate model.

using namespace delta;

namespace {

// §16.4.1: a passing observed (#0) deferred assertion's pass action is a
// pending report -- deferred, not run inline -- so its effect still lands by
// end of the time step. The assignment following the assert would clobber a
// same-region write, so observing x==44 shows the pass action ran after the
// process settled.
TEST(AssertionStatementSim, DeferredAssertHash0) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assert #0 (1) x = 8'd44;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 44u);
}

// §16.4.1: an observed deferred assert that fails with no else clause reports
// via $error, and that report is deferred (executed in the Reactive region),
// not emitted at the point the assert is processed. The $error("later") that
// follows runs immediately in the Active region, so if the deferred report were
// emitted inline it would be overwritten by "later"; observing "Assertion
// failed." as the last severity proves the default report was deferred past the
// inline severity.
TEST(DeferredAssertionReporting, ObservedDefaultErrorReportIsDeferred) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    assert #0 (0);\n"
      "    $error(\"later\");\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverity(), "ERROR");
  EXPECT_EQ(f.ctx.LastSeverityMsg(), "Assertion failed.");
}

// §16.4.1: a final deferred assert failing with no else clause defers its
// default $error too, but to the Postponed region -- even later than an
// observed report. Same probe as above: the inline $error("later") must not be
// the last severity.
TEST(DeferredAssertionReporting, FinalDefaultErrorReportIsDeferred) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    assert final (0);\n"
      "    $error(\"later\");\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverity(), "ERROR");
  EXPECT_EQ(f.ctx.LastSeverityMsg(), "Assertion failed.");
}

// §16.4.1 lists "assert or assume" for the default $error report path, so a
// failing observed deferred assume with no else clause defers its report the
// same way an assert does.
TEST(DeferredAssertionReporting, DeferredAssumeDefaultErrorReportIsDeferred) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    assume #0 (0);\n"
      "    $error(\"later\");\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverity(), "ERROR");
  EXPECT_EQ(f.ctx.LastSeverityMsg(), "Assertion failed.");
}

// §16.4.1: an observed deferred report is executed in the Reactive region while
// a final deferred report is executed in the (later) Postponed region. The
// final assert appears FIRST in source here, yet its else action runs LAST: r
// ends at 2 because the observed report (r=1) matures in Reactive and the final
// report (r=2) is scheduled into the subsequent Postponed region. If both
// reports ran in the same region, source order would leave r==1.
TEST(DeferredAssertionReporting, FinalReportRunsAfterObservedReport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r = 0;\n"
      "  initial begin\n"
      "    assert final (0) else r = 2;\n"
      "    assert #0 (0) else r = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// §16.4.1: the pending-report rule applies to every deferred directive, not
// just assert/assume. A deferred cover's action (its pass statement) is also a
// pending report rather than run inline. cover #0 (1) matches, so `hits = hits
// + 1` is deferred to the Reactive region; the inline `hits = 5` that follows
// runs first, so the deferred increment observes 5 and leaves hits==6. Were the
// cover action run inline it would set hits=1 and be clobbered to 5.
TEST(DeferredAssertionReporting, DeferredCoverActionIsPendingReport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int hits = 0;\n"
      "  initial begin\n"
      "    cover #0 (1) hits = hits + 1;\n"
      "    hits = 5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("hits");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 6u);
}

// §16.4.1: a final deferred assertion defers its PASS action too, into the
// Postponed region. assert final (1) matches, so `r = 1` becomes a pending
// report while the following `r = 5` runs inline in the Active region; the
// Postponed action then overwrites it, leaving r==1. Run inline, the pass
// action would set r=1 and be clobbered to 5.
TEST(DeferredAssertionReporting, FinalPassActionDeferredToPostponed) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r = 0;\n"
      "  initial begin\n"
      "    assert final (1) r = 1;\n"
      "    r = 5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §16.4.1: the final deferral applies to the cover directive as well -- a
// cover final action is scheduled into the Postponed region. cover final (1)
// matches, so `hits = 1` is deferred past the inline `hits = 9`, leaving
// hits==1.
TEST(DeferredAssertionReporting, FinalCoverActionDeferredToPostponed) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int hits = 0;\n"
      "  initial begin\n"
      "    cover final (1) hits = 1;\n"
      "    hits = 9;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("hits");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §16.4.1 (negative form): a report is placed in the queue only when the
// assertion passes or fails with an action to run. A passing observed deferred
// assert with no pass statement queues nothing, so no report -- and no severity
// -- is ever produced.
TEST(DeferredAssertionReporting, PassingDeferredAssertProducesNoReport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial assert #0 (1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverity(), "");
}

}  // namespace
