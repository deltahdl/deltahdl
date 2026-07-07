#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(LevelSensitiveEventSimulation, WaitConditionBlocks) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic ready;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    ready = 0;\n"
      "    #10 ready = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    wait (ready) x = 8'd88;\n"
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

TEST(LevelSensitiveEventSimulation, WaitAlreadyTrue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    wait (1) x = 8'd11;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 11u);
}

TEST(LevelSensitiveEventSimulation, WaitStatementNullBody) {
  auto val = RunAndGet(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    wait(1) ;\n"
      "    x = 8'd77;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 77u);
}

TEST(LevelSensitiveEventSimulation, WaitXConditionBlocks) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic cond;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    cond = 1'bx;\n"
      "    x = 8'd0;\n"
      "    wait (cond) x = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 0u);
}

TEST(LevelSensitiveEventSimulation, WaitConditionWithDelayInBody) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic enable;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    enable = 0;\n"
      "    b = 8'd55;\n"
      "    #5 enable = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    wait (!enable) #10 a = b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

TEST(LevelSensitiveEventSimulation, WaitMultipleSignalCondition) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic a, b;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    a = 0;\n"
      "    b = 0;\n"
      "    #5 a = 1;\n"
      "    #5 b = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    wait (a && b) x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 99u);
}

TEST(LevelSensitiveEventSimulation, WaitZeroConditionNeverUnblocks) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    wait (0) x = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 0u);
}

// A variable condition already satisfied when the wait is reached must let the
// following statement run without ever suspending the process.
TEST(LevelSensitiveEventSimulation, WaitVariableAlreadyTrueProceeds) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic flag;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    flag = 1;\n"
      "    x = 8'd0;\n"
      "    wait (flag) x = 8'd200;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 200u);
}

// A multi-bit condition follows the same truthiness rule as a scalar: it is
// false while zero and becomes true once any bit is set, releasing the wait.
TEST(LevelSensitiveEventSimulation, WaitVectorNonzeroConditionUnblocks) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [3:0] cnt;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    cnt = 4'd0;\n"
      "    x = 8'd0;\n"
      "    #5 cnt = 4'd6;\n"
      "  end\n"
      "  initial begin\n"
      "    wait (cnt) x = 8'd123;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 123u);
}

// The clause requires that the statements *following* a wait remain blocked
// until the condition holds. With a null body, the observable is the next
// statement in the enclosing block. `tag` is latched to 77 one time step before
// `ready` rises, so a process that correctly suspends copies 77; one that ran
// at time 0 (never blocking) would have copied the initial 10. The distinct
// final value is what proves the following statement was actually held off.
TEST(LevelSensitiveEventSimulation, WaitNullBodyBlocksFollowingStatement) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic ready;\n"
      "  logic [7:0] tag, x;\n"
      "  initial begin\n"
      "    ready = 0;\n"
      "    tag = 8'd10;\n"
      "    #5  tag = 8'd77;\n"
      "    #5  ready = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    wait (ready) ;\n"
      "    x = tag;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 77u);
}

// The blocking branch of the clause's example: `enable` is 1 on entry, so
// wait(!enable) must suspend and only release once it clears. `b` is latched to
// 55 a time step before that release, so the delayed body `#10 a = b`
// copies 55. If the wait had failed to block, `a` would remain 0 because the
// condition is false at time 0. Complements WaitConditionWithDelayInBody, which
// exercises the already-true (no-block) branch of the same example.
TEST(LevelSensitiveEventSimulation, WaitBlocksThenDelayedBodyExecutes) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic enable;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    enable = 1;\n"
      "    b = 8'd10;\n"
      "    #5  b = 8'd55;\n"
      "    #5  enable = 0;\n"
      "  end\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    wait (!enable) #10 a = b;\n"
      "  end\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(val, 55u);
}

// statement_or_null may be a begin-end block; after the wait releases, every
// statement in the block must run. `src` is latched to 9 one time step before
// `go` rises, so a correctly blocked process copies 9 into both members of the
// block (the second assignment reads the first), proving the whole block body
// executed post-release. A process that never blocked would have copied 1.
TEST(LevelSensitiveEventSimulation, WaitBlockBodyExecutesAfterUnblock) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic go;\n"
      "  logic [7:0] src, p, q;\n"
      "  initial begin\n"
      "    go = 0;\n"
      "    src = 8'd1;\n"
      "    #5  src = 8'd9;\n"
      "    #5  go = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    p = 8'd0;\n"
      "    q = 8'd0;\n"
      "    wait (go) begin\n"
      "      p = src;\n"
      "      q = p;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      "q");
  EXPECT_EQ(val, 9u);
}

// The condition may be any integral expression, including a 2-state type. A
// zero `int` is false and blocks; once it becomes nonzero the wait releases and
// the following statement runs. This drives the §12.4 truth rule through a
// 2-state operand rather than the 4-state `logic` used by the other tests.
TEST(LevelSensitiveEventSimulation, WaitTwoStateIntConditionUnblocks) {
  auto val = RunAndGet(
      "module t;\n"
      "  int count;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    count = 0;\n"
      "    x = 8'd0;\n"
      "    #5 count = 3;\n"
      "  end\n"
      "  initial begin\n"
      "    wait (count) x = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 42u);
}

}  // namespace
