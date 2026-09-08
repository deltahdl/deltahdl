#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(LevelSensitiveEventSimulation, WaitConditionBlocks) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 88u);
}

TEST(LevelSensitiveEventSimulation, WaitAlreadyTrue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    wait (1) x = 8'd11;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
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
  auto* var = RunAndFindVar(
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
      f, "a");
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

// §9.4.3: "the wait statement shall evaluate a condition; if it is false, the
// procedural statements following the wait statement shall remain blocked until
// that condition becomes true." Every case above writes its condition on a
// whole variable. This one writes it on a single bit, which is the operand
// whose collected name is BuildSelectPrefix's `v[1]` -- a position within a
// vector, which SimContext::FindVariable resolves to no object, so
// ExecWaitStatement armed no watcher and the condition was never re-tested.
//
// v starts all zero and x starts at 0, so a wait that never resumes leaves x
// at 0 rather than at 42, and only the bit the condition reads is set at time
// 10.
TEST(LevelSensitiveEventSimulation, WaitOnABitSelectResumesWhenThatBitChanges) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    v = 4'b0000;\n"
      "    x = 8'd0;\n"
      "    #10 v = 4'b0010;\n"
      "  end\n"
      "  initial begin\n"
      "    wait (v[1]) x = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 42u);
}

// §9.4.3 states level-sensitive event control as an obligation about the truth
// of a condition rather than as a reaction to a change: "The wait statement
// shall evaluate a condition; and, if it is not true (as defined in 12.4), the
// procedural statements following the wait statement shall remain blocked
// until that condition becomes true before continuing." The clause draws the
// contrast itself -- the wait is "level-sensitive, as opposed to basic event
// control (specified by the @ character), which is edge-sensitive" -- so a
// §9.4.2 case does not stand in for this one: any route that observes the
// condition becoming true would satisfy §9.4.3. In this implementation,
// though, a wait parks on the same AnyChangeAwaiter that @ parks on and is
// released only by the written variable's watcher notification, so the two
// mechanisms fail together, which is what earns this clause its own case.
//
// The writer has to be a void function called with parentheses, because that
// is the only call form whose body runs through ExecFunctionBody and its
// identifier-assignment path. A task call is inlined onto the ordinary
// statement executor, which notifies already, so a task written here would
// pass whether or not the function path notifies and would prove nothing.
//
// `done` holds 8'd3 when the process parks and the wait's body writes 8'd91,
// neither of them a value a `logic [7:0]` reaches on its own, so a process
// left parked for the rest of the run reads back as 3 rather than 91.
TEST(LevelSensitiveEventSimulation, WaitResumesOnVoidFunctionWrite) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic gate;\n"
      "  logic [7:0] done;\n"
      "  function void open_gate;\n"
      "    gate = 1'b1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    gate = 1'b0;\n"
      "    #5;\n"
      "    open_gate();\n"
      "  end\n"
      "  initial begin\n"
      "    done = 8'd3;\n"
      "    wait (gate) done = 8'd91;\n"
      "  end\n"
      "endmodule\n",
      f, "done");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 91u);
}

}  // namespace
