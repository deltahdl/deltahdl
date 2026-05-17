#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// --- §16.3 Assert: pass/fail action execution ---

TEST(ImmediateAssertSim, AssertTrueExecutesPassAction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assert(1) x = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(ImmediateAssertSim, AssertFalseExecutesFailAction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assert(0) x = 8'd42; else x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(ImmediateAssertSim, AssertTrueSkipsFailAction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assert(1) x = 8'd42; else x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(ImmediateAssertSim, AssertTrueWithNoActionsCompletes) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    assert(1);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(ImmediateAssertSim, AssertFalseElseOnlyExecutesFail) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assert(0) else x = 8'd77;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(ImmediateAssertSim, AssertWithBeginEndBlock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assert(1) begin x = 8'd88; end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 88u);
}

TEST(ImmediateAssertSim, MultipleAssertionsSequential) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assert(1) x = 8'd10;\n"
      "    assert(1) x = x + 8'd5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

TEST(ImmediateAssertSim, AssertNonzeroValueSucceeds) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assert(42) x = 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ImmediateAssertSim, AssertConditionFromVariable) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, flag;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    flag = 8'd0;\n"
      "    assert(x == 8'd5) flag = 8'd1; else flag = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("flag");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// --- §16.3 Default $error when assert fails without else clause ---

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
  // User-provided else clause runs; no default $error.
  EXPECT_EQ(f.ctx.AssertionFailCount(), 0);
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// --- §16.3 Assume: same behavior as assert in simulation ---

TEST(ImmediateAssertSim, AssumeTrueExecutesPassAction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assume(1) x = 8'd50;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 50u);
}

TEST(ImmediateAssertSim, AssumeFalseExecutesFailAction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    assume(0) x = 8'd50; else x = 8'd60;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 60u);
}

// --- §16.3 Cover: pass action on true, no action on false ---

TEST(ImmediateAssertSim, CoverTrueExecutesPassAction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    cover(1) x = 8'd70;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 70u);
}

TEST(ImmediateAssertSim, CoverFalseSkipsPassAction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    cover(0) x = 8'd70;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
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
  // Cover does NOT emit default $error on false — it only tracks coverage.
  EXPECT_EQ(f.ctx.AssertionFailCount(), 0);
}

TEST(ImmediateAssertSim, CoverTrueWithNoActionsCompletes) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd3;\n"
      "    cover(1);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

// --- §16.3 "If the expression evaluates to x, z, or 0, then it is
// interpreted as being false." ---

TEST(ImmediateAssertSim, AssertXValueIsFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic v;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    v = 1'bx;\n"
      "    assert(v) x = 8'd11; else x = 8'd22;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 22u);
}

TEST(ImmediateAssertSim, AssertZValueIsFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic v;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    v = 1'bz;\n"
      "    assert(v) x = 8'd33; else x = 8'd44;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 44u);
}

// --- §16.3 "The results of coverage for an immediate cover statement shall
// contain... Number of times evaluated, Number of times succeeded." ---

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
  EXPECT_EQ(f.ctx.CoverEvalCount(), 3);
  EXPECT_EQ(f.ctx.CoverSuccessCount(), 2);
}

// --- §16.3 cross-link to §20.10: the default $error path on a failing
// assert with no else clause must route through the shared severity-task
// emitter and record itself in SimContext. ---

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

// --- §16.3 "A simulation tool shall provide the capability to treat an
// immediate assume statement as an immediate assert statement in order to
// verify that the environment behaves as assumed." ---
//
// Assume must drive the same failure machinery as assert (default $error and
// fail counter) so the tool can flip-treat one for the other.

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

// --- §16.3 "The severity system tasks can be used in assertion pass or
// fail statements. These tasks shall print the same tool-specific message
// when used either in a pass or a fail statement." ---
//
// Same $error("oops") in pass vs fail must produce the same captured msg.

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

// --- §16.3 "If more than one of these system tasks is included in the
// action block, then each shall be executed as specified." ---
//
// Two severity tasks in a single fail block must each emit; the second
// overwrites the captured snapshot, which proves both ran in order.

// --- §16.3 "If the severity system task is executed at a time other than
// when the immediate assert or assume fails, the actual failure time of the
// immediate assert or assume can be recorded and displayed programmatically."
// ---
//
// Capture $time in the fail action so the failure time survives even when
// the severity report is emitted later.

TEST(ImmediateAssertSim, FailureTimeRecordableInActionBlock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [63:0] fail_time;\n"
      "  initial begin\n"
      "    fail_time = 64'd0;\n"
      "    #10 assert(0) else fail_time = $time;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("fail_time");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(ImmediateAssertSim, MultipleSeverityTasksInActionBlockBothRun) {
  SimFixture f;
  auto* design = ElaborateSrc(
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
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  // Both tasks ran: x was set between them, and the last captured severity
  // is the second task's "WARNING".
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
  EXPECT_EQ(f.ctx.LastSeverity(), "WARNING");
  EXPECT_EQ(f.ctx.LastSeverityMsg(), "second");
}

}  // namespace
