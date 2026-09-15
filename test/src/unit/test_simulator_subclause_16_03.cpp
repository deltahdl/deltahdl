#include <sstream>
#include <string>

#include "fixture_simulator.h"
#include "simulator/immediate_cover.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ImmediateAssertSim, AssertTrueExecutesPassAction) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assert(1) x = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(ImmediateAssertSim, AssertFalseExecutesFailAction) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assert(0) x = 8'd42; else x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(ImmediateAssertSim, AssertTrueSkipsFailAction) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assert(1) x = 8'd42; else x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(ImmediateAssertSim, AssertTrueWithNoActionsCompletes) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    assert(1);\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(ImmediateAssertSim, AssertFalseElseOnlyExecutesFail) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assert(0) else x = 8'd77;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(ImmediateAssertSim, AssertWithBeginEndBlock) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assert(1) begin x = 8'd88; end\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 88u);
}

TEST(ImmediateAssertSim, MultipleAssertionsSequential) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assert(1) x = 8'd10;\n"
      "    assert(1) x = x + 8'd5;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

TEST(ImmediateAssertSim, AssertNonzeroValueSucceeds) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assert(42) x = 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ImmediateAssertSim, AssertConditionFromVariable) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x, flag;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    flag = 8'd0;\n"
      "    assert(x == 8'd5) flag = 8'd1; else flag = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f, "flag");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ImmediateAssertSim, AssertTrueNoElseDoesNotIncrementFailCount) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    assert(1);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.AssertionFailCount(), 0);
}

TEST(ImmediateAssertSim, AssertFalseWithElseNoDefaultError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assert(0) else x = 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  EXPECT_EQ(f.ctx.AssertionFailCount(), 0);
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ImmediateAssertSim, AssumeTrueExecutesPassAction) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assume(1) x = 8'd50;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 50u);
}

TEST(ImmediateAssertSim, AssumeFalseExecutesFailAction) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assume(0) x = 8'd50; else x = 8'd60;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 60u);
}

TEST(ImmediateAssertSim, CoverTrueExecutesPassAction) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    cover(1) x = 8'd70;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 70u);
}

TEST(ImmediateAssertSim, CoverFalseSkipsPassAction) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    cover(0) x = 8'd70;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(ImmediateAssertSim, CoverFalseNoDefaultError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    cover(0);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  EXPECT_EQ(f.ctx.AssertionFailCount(), 0);
}

TEST(ImmediateAssertSim, CoverTrueWithNoActionsCompletes) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd3;\n"
      "    cover(1);\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(ImmediateAssertSim, AssertXValueIsFalse) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic v;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    v = 1'bx;\n"
      "    assert(v) x = 8'd11; else x = 8'd22;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 22u);
}

TEST(ImmediateAssertSim, AssertZValueIsFalse) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic v;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    v = 1'bz;\n"
      "    assert(v) x = 8'd33; else x = 8'd44;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 44u);
}

TEST(ImmediateAssertSim, CoverEvaluationAndSuccessCountsTracked) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    cover(1);\n"
      "    cover(0);\n"
      "    cover(1);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.ImmediateCovers().Evaluated(), 3u);
  EXPECT_EQ(f.ctx.ImmediateCovers().Succeeded(), 2u);
}

TEST(ImmediateAssertSim, DefaultErrorRecordsSeverityViaSharedHelper) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial assert(0);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.AssertionFailCount(), 1);
  EXPECT_EQ(f.ctx.LastSeverity(), "ERROR");
}

TEST(ImmediateAssertSim, AssumeFailureDrivesSameMachineryAsAssert) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    assume(0);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.AssertionFailCount(), 1);
  EXPECT_EQ(f.ctx.LastSeverity(), "ERROR");
}

TEST(ImmediateAssertSim, SeverityTaskSameMessageInPassAction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial assert(1) $error(\"oops\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.LastSeverity(), "ERROR");
  EXPECT_EQ(f.ctx.LastSeverityMsg(), "oops");
}

TEST(ImmediateAssertSim, SeverityTaskSameMessageInFailAction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial assert(0) $info(\"ok\"); else $error(\"oops\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.LastSeverity(), "ERROR");
  EXPECT_EQ(f.ctx.LastSeverityMsg(), "oops");
}

TEST(ImmediateAssertSim, FailureTimeRecordableInActionBlock) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [63:0] fail_time;\n"
      "  initial begin\n"
      "    fail_time = 64'd0;\n"
      "    #10 assert(0) else fail_time = $time;\n"
      "  end\n"
      "endmodule\n",
      f, "fail_time");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

// §16.3: the execution of immediate assertions can be controlled by using the
// assertion control system tasks (§20.11). With $assertoff in effect the
// assertion is not checked, so neither its pass nor its fail (else) action
// runs; $asserton restores checking and the fail action runs. Built from real
// source and driven through the full pipeline.
TEST(ImmediateAssertSim, ControlledByAssertionControlSystemTask) {
  SimFixture off;
  auto* xo = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    $assertoff;\n"
      "    assert(0) else x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      off, "x");
  ASSERT_NE(xo, nullptr);
  EXPECT_EQ(xo->value.ToUint64(), 0u);  // fail action suppressed while off

  SimFixture on;
  auto* xn = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    $assertoff;\n"
      "    $asserton;\n"
      "    assert(0) else x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      on, "x");
  ASSERT_NE(xn, nullptr);
  EXPECT_EQ(xn->value.ToUint64(), 99u);  // fail action runs once re-enabled
}

TEST(ImmediateAssertSim, MultipleSeverityTasksInActionBlockBothRun) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assert(0) else begin\n"
      "      $error(\"first\");\n"
      "      x = 8'd55;\n"
      "      $warning(\"second\");\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
  EXPECT_EQ(f.ctx.LastSeverity(), "WARNING");
  EXPECT_EQ(f.ctx.LastSeverityMsg(), "second");
}

// §16.3: the fail statement, being any legal procedural statement, can signal a
// failure to another part of the testbench. Here a failing assert triggers an
// event that a separate process is waiting on, and that process then runs.
// Built from real source and driven end to end.
TEST(ImmediateAssertSim, FailActionTriggersEventUnblockingProcess) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event ev;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    #1 assert(0) else -> ev;\n"
      "  end\n"
      "  always @(ev) x = 8'd42;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// §16.3: the asserted expression is interpreted like an if condition, and it
// may be any nontemporal expression -- including a function call. Here the
// condition is a user function returning false, so the assertion fails and the
// else arm runs. Built from real source and driven end to end.
TEST(ImmediateAssertSim, AssertConditionFromFunctionCall) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] flag;\n"
      "  function logic is_hi(input logic [7:0] v);\n"
      "    is_hi = (v > 8'd4);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 8'd3;\n"
      "    flag = 8'd0;\n"
      "    assert(is_hi(x)) flag = 8'd1; else flag = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f, "flag");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);  // is_hi(3) is false -> else arm
}

// §16.3: when the severity task runs at a time other than the failure's, the
// failure time recorded in the action block is what the message prints. The
// clause's own example records $time into t, delays the $error by 5, and says
// the message printed at 15 reads "assert failed at time 10". The example
// writes the time through %0t, so the string is the clause's only where a 0
// field width prints the time with no leading spaces; padded to Table 20-3's
// 20-column default the string would not be the one the clause gives. $info
// stands in for the example's $error so std::cout carries the message, and the
// tool-specific header the same $info emits goes ahead of it on the line, so
// the check is for the clause's string at the end of the header's line.
TEST(ImmediateAssertSim, DelayedSeverityTaskPrintsTheRecordedFailureTime) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  time fail_time;\n"
      "  initial begin\n"
      "    #10 assert (0) else begin\n"
      "      fail_time = $time;\n"
      "      #5 $info(\"assert failed at time %0t\", fail_time);\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find(": assert failed at time 10\n"), std::string::npos);
  EXPECT_EQ(out.find("assert failed at time  "), std::string::npos);
  EXPECT_EQ(out.rfind("[15]", 0), 0u);
}

// §16.3: the results of coverage for an immediate cover statement contain the
// number of times it was evaluated and the number of times it succeeded, and a
// tool reports them at the end of simulation. Two statements in a loop of
// three, one holding on every pass and one on none, so the two records differ
// from each other and from a count kept over all cover statements together;
// the report names each by its scope and line, and the label the second one
// carries is in its scope, as §16.3 has the label create a named block around
// the statement.
TEST(ImmediateAssertSim, CoverResultsAreReportedPerStatementAtEndOfSimulation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int i;\n"
      "  initial begin\n"
      "    for (i = 0; i < 3; i = i + 1) begin\n"
      "      cover (i < 3);\n"
      "      never: cover (i > 3);\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  std::ostringstream report;
  ReportImmediateCoverResults(f.ctx.ImmediateCovers(), report);
  EXPECT_EQ(report.str(),
            "cover t (line 5): evaluated 3, succeeded 3\n"
            "cover t.never (line 6): evaluated 3, succeeded 0\n");
}

// §16.3's results are the immediate cover statement's. A cover property in the
// clocked boolean form is lowered to the same statement kind inside a clocked
// process, but it is a concurrent cover, whose results §16.14.3 defines as
// attempts, successes and vacuous successes, so it leaves the immediate
// results empty however many ticks it is evaluated at.
TEST(ImmediateAssertSim, CoverPropertyIsNotAnImmediateCoverResult) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk = 1'b0;\n"
      "  cover property (@(posedge clk) clk);\n"
      "  initial begin\n"
      "    #5 clk = 1;\n"
      "    #5 clk = 0;\n"
      "    #5 clk = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(f.ctx.ImmediateCovers().Results().empty());
}

}  // namespace
