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

// Every deferred action below is a single subroutine call, because §16.4 says
// "the pass and fail statements in a deferred assertion's action_block, if
// present, shall each consist of a single subroutine call" -- an assignment is
// not one. An observed (#0) action calls a void function that writes the
// variable under test, which is legal because §16.4 schedules that call in the
// Reactive region. A final action cannot use that vehicle: §16.4 requires its
// subroutine to "be one that may be legally called in the Postponed region",
// and §4.4.2.9 says of that region that "it is illegal to write values to any
// net or variable", so the final tests report through a severity system task
// and observe it with LastSeverity() and LastSeverityMsg().

// §16.4.1: a passing observed (#0) deferred assertion's pass action is a
// pending report -- deferred, not run inline -- so its effect still lands by
// end of the time step. The assignment following the assert would clobber a
// same-region write, so observing x==44 shows the pass action ran after the
// process settled.
TEST(AssertionStatementSim, DeferredAssertHash0) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  function void set_x_44; x = 8'd44; endfunction\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assert #0 (1) set_x_44();\n"
      "  end\n"
      "endmodule\n",
      f, "x");
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
// final assert appears FIRST in source here, yet its else action runs LAST: the
// observed report ("observed") matures in Reactive and the final report
// ("final") is scheduled into the subsequent Postponed region, so "final" is
// the last severity recorded. If both reports ran in the same region, source
// order would leave "observed" last instead.
TEST(DeferredAssertionReporting, FinalReportRunsAfterObservedReport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    assert final (0) else $error(\"final\");\n"
      "    assert #0 (0) else $error(\"observed\");\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverityMsg(), "final");
}

// §16.4.1: the pending-report rule applies to every deferred directive, not
// just assert/assume. A deferred cover's action (its pass statement) is also a
// pending report rather than run inline. cover #0 (1) matches, so the bump()
// call is deferred to the Reactive region; the inline `hits = 5` that follows
// runs first, so the deferred increment observes 5 and leaves hits==6. Were the
// cover action run inline it would set hits=1 and be clobbered to 5.
TEST(DeferredAssertionReporting, DeferredCoverActionIsPendingReport) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int hits = 0;\n"
      "  function void bump; hits = hits + 1; endfunction\n"
      "  initial begin\n"
      "    cover #0 (1) bump();\n"
      "    hits = 5;\n"
      "  end\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 6u);
}

// §16.4.1: a final deferred assertion defers its PASS action too, into the
// Postponed region. assert final (1) matches, so its $info becomes a pending
// report while the $error that follows runs inline in the Active region; the
// Postponed report then runs last, so the last severity is INFO. Run inline,
// the pass action would report first and ERROR would be last.
TEST(DeferredAssertionReporting, FinalPassActionDeferredToPostponed) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    assert final (1) $info(\"final pass\");\n"
      "    $error(\"inline\");\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverity(), "INFO");
}

// §16.4.1: the final deferral applies to the cover directive as well -- a
// cover final action is scheduled into the Postponed region. cover final (1)
// matches, so its $warning is deferred past the inline $error, leaving WARNING
// as the last severity.
TEST(DeferredAssertionReporting, FinalCoverActionDeferredToPostponed) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    cover final (1) $warning(\"covered late\");\n"
      "    $error(\"inline\");\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.LastSeverity(), "WARNING");
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
