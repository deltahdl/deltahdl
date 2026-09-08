#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(LoopStatementSim, ForBasic) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] total;\n"
      "  initial begin\n"
      "    total = 8'd0;\n"
      "    for (int i = 0; i < 5; i = i + 1)\n"
      "      total = total + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "total");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(LoopStatementSim, ForTypedInit) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] sum;\n"
      "  initial begin\n"
      "    sum = 8'd0;\n"
      "    for (int i = 1; i <= 4; i = i + 1)\n"
      "      sum = sum + i[7:0];\n"
      "  end\n"
      "endmodule\n",
      f, "sum");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(LoopStatementSim, ForAllEmptyWithBreak) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    for (;;) begin\n"
      "      if (x == 8'd4) break;\n"
      "      x = x + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

TEST(LoopStatementSim, ProcessWithLoop) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [15:0] sum;\n"
      "  initial begin\n"
      "    integer i;\n"
      "    sum = 0;\n"
      "    for (i = 1; i <= 5; i = i + 1)\n"
      "      sum = sum + i[15:0];\n"
      "  end\n"
      "endmodule\n",
      "sum");

  EXPECT_EQ(result, 15u);
}

// A continue hands control to the next iteration of the for-loop, so the
// step assignment and control expression of 12.7.1 still carry the loop
// through its remaining iterations. The 12.8 file covers continue as a jump
// statement.
TEST(LoopStatementSim, ForContinueAdvancesToNextIteration) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] sum;\n"
      "  initial begin\n"
      "    sum = 8'd0;\n"
      "    for (int i = 0; i < 6; i++) begin\n"
      "      if (i == 3) continue;\n"
      "      sum = sum + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "sum");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(LoopStatementSim, ForNested) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] cnt;\n"
      "  initial begin\n"
      "    cnt = 8'd0;\n"
      "    for (int i = 0; i < 3; i++)\n"
      "      for (int j = 0; j < 4; j++)\n"
      "        cnt = cnt + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "cnt");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 12u);
}

TEST(LoopStatementSim, ForZeroIterations) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd42;\n"
      "    for (int i = 10; i < 5; i++)\n"
      "      x = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(LoopStatementSim, ForDecrement) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] last;\n"
      "  initial begin\n"
      "    last = 8'd0;\n"
      "    for (int i = 5; i > 0; i--)\n"
      "      last = i[7:0];\n"
      "  end\n"
      "endmodule\n",
      f, "last");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(LoopStatementSim, ForXConditionExitsImmediately) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic cond;\n"
      "  initial begin\n"
      "    x = 8'd42;\n"
      "    cond = 1'bx;\n"
      "    for (int i = 0; cond; i++)\n"
      "      x = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(LoopStatementSim, ForZConditionExitsImmediately) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic cond;\n"
      "  initial begin\n"
      "    x = 8'd42;\n"
      "    cond = 1'bz;\n"
      "    for (int i = 0; cond; i++)\n"
      "      x = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(LoopStatementSim, ForCommaSeparatedInitAndStep) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = 0;\n"
      "    for (int i = 0, int j = 4; i < j; i++, j--)\n"
      "      result = result + 1;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 2u);
}

// When a for-loop initialization declares several locals, a later local's
// initializer can read an earlier local. Here j starts at i + 3 == 3, so the
// loop runs for i = 0..2 and the body executes three times.
TEST(LoopStatementSim, ForLaterLocalInitUsesEarlierLocal) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    result = 0;\n"
      "    for (int i = 0, int j = i + 3; i < j; i++)\n"
      "      result = result + 1;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(val, 3u);
}

// §12.7.1 step c) admits a function call as a for_step form, alongside
// assignment statements and increment/decrement expressions. Here the step is a
// void function call that advances the loop-control variable through an inout
// argument, so the loop runs while i < 4 and the body executes four times. This
// observes the function-call step actually executing at run time, not merely
// parsing.
TEST(LoopStatementSim, ForFunctionCallStepAdvancesLoop) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [7:0] i;\n"
      "  logic [7:0] cnt;\n"
      "  function void bump(inout logic [7:0] v);\n"
      "    v = v + 8'd1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    i = 8'd0;\n"
      "    cnt = 8'd0;\n"
      "    for (i = 0; i < 4; bump(i))\n"
      "      cnt = cnt + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      "cnt");
  EXPECT_EQ(val, 4u);
}

// The implicit block created by a for-loop's local declaration can be named
// with a statement label; the labeled loop runs normally.
TEST(LoopStatementSim, ForLabeledLoopRuns) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] total;\n"
      "  initial begin\n"
      "    total = 8'd0;\n"
      "    counting : for (int i = 0; i < 5; i = i + 1)\n"
      "      total = total + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "total");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

// §12.7.1 has the for statement declare its control variable in the loop's own
// implicit block -- "the loop variable is local to the loop" -- so `for (int i
// = seed; ...)` declares a storage element of its own and §6.8's "A variable
// shall store a value from one assignment to the next" holds for `seed` across
// the whole loop: the header reads it once and no part of the loop names it
// again. ExecFuncForInits stored what EvalExpr answered, EvalExpr answers a
// bare identifier with the source variable's own Logic4Vec, and a Logic4Vec
// copies its `words` pointer rather than the words, so the header left `i` and
// `seed` one element. This site does not even resize on the way in, so unlike
// a body declaration it shares the buffer at any width the source has.
//
// The loop is written inside a function body because that is where this
// header's variables are created: ExecFuncForInits builds them for a for in a
// subroutine body and CreateForInitVars for one in a procedural block, so a
// loop in an initial block reaches a different site and states nothing about
// this one.
//
// What the loop does to `i` afterwards is not what exposes the sharing, and
// the case is shaped around that. The step `i = i + 1` computes a new vector
// and ExecFuncIdentifierAssign puts it in the local's place, which leaves
// `seed`'s buffer unreferenced rather than writing through it. The writer that
// does reach it is the one that converts a vector it did not build: §13.5.1
// copies "the values of the actual arguments" into an input formal, and
// §6.11.2 -- "any unknown or high-impedance bits shall be converted to zeros"
// -- converts that copy in place, so handing the loop variable to a `bit
// [7:0]` formal cleared `seed`'s unknowns in the iteration that only read it.
//
// That the conversion reaches the actual's own buffer is a defect of this
// same family at the binding site (#3564), and it is what makes this case
// discriminating rather than merely true: with the binding taking its own
// copy, the conversion would land on that copy whether or not the
// header above shared its words, and the case would go on holding with
// nothing left to expose the sharing. No writer in the tree reaches a plain
// integral local's buffer in place, so this is the exposure the claim has.
//
// The loop runs exactly once and its termination is the step's alone: `seed`
// has an even low nibble, so `i[0] == 1'b0` admits the first iteration, and
// after `i = i + 1` the low bit is 1 -- or the whole of `i` is x, once the
// unknowns above it survive into the sum -- and either answer ends the loop.
//
// ToUint64 projects aval & ~bval, so an unknown bit reads as 0 through it and
// clearing it changes nothing it reports; the assertions read words[0].
// 8'b1x0z0000 is stored as aval 0xC0 with bval 0x50, an x digit being aval 1
// with bval 1 and a z digit aval 0 with bval 1, and the 2-state conversion of
// it is aval 0x80 with bval 0x00 -- which is what the formal, and `noticed`
// after it, alone are entitled to hold.
TEST(LoopStatementSim, ForHeaderLocalInitializedFromAVariableGetsItsOwnWords) {
  SimFixture f;
  auto* source = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] seed;\n"
      "  bit [7:0] noticed;\n"
      "  function bit [7:0] pass_on(bit [7:0] step_val);\n"
      "    return step_val;\n"
      "  endfunction\n"
      "  function void sweep();\n"
      "    for (int i = seed; i[0] == 1'b0; i = i + 1)\n"
      "      noticed = pass_on(i);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    seed = 8'b1x0z0000;\n"
      "    sweep();\n"
      "  end\n"
      "endmodule\n",
      f, "seed");
  ASSERT_NE(source, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* seen_in_loop = f.ctx.FindVariable("noticed");
  ASSERT_NE(seen_in_loop, nullptr);
  EXPECT_EQ(source->value.words[0].aval & 0xFFu, 0xC0u);
  EXPECT_EQ(source->value.words[0].bval & 0xFFu, 0x50u);
  EXPECT_EQ(seen_in_loop->value.words[0].aval & 0xFFu, 0x80u);
  EXPECT_EQ(seen_in_loop->value.words[0].bval & 0xFFu, 0x00u);
}

}  // namespace
