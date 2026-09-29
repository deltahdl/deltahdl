#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(LoopStatementSim, RepeatCount) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    repeat (5) x = x + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(LoopStatementSim, RepeatZero) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd42;\n"
      "    repeat (0) x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(LoopStatementSim, RepeatBlock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    b = 8'd0;\n"
      "    repeat (3) begin\n"
      "      a = a + 8'd1;\n"
      "      b = b + 8'd2;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 3u);
  EXPECT_EQ(vb->value.ToUint64(), 6u);
}

TEST(LoopStatementSim, RepeatVariableCount) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] n, x;\n"
      "  initial begin\n"
      "    n = 8'd4;\n"
      "    x = 8'd0;\n"
      "    repeat (n) x = x + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

TEST(LoopStatementSim, RepeatExpressionCount) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic [7:0] total;\n"
      "  logic [7:0] n;\n"
      "  initial begin\n"
      "    n = 8'd3;\n"
      "    total = 8'd0;\n"
      "    repeat (n + 8'd2)\n"
      "      total = total + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "total");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(LoopStatementSim, RepeatXCountZeroIterations) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] n;\n"
      "  initial begin\n"
      "    x = 8'd42;\n"
      "    n = 8'bx;\n"
      "    repeat (n) x = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(LoopStatementSim, RepeatNegativeCountZeroIterations) {
  // §12.7.2: a negative count (signed expression) is treated as zero, so the
  // body never runs. Without negative handling, the bit pattern of -1 would be
  // read as a huge unsigned iteration count.
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int n;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd42;\n"
      "    n = -1;\n"
      "    repeat (n) x = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(LoopStatementSim, RepeatCountEvaluatedOnceBeforeLoop) {
  // §12.7.2: the count expression is evaluated once before the loop starts;
  // mutating the controlling variable inside the body has no effect on the
  // number of iterations.
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] n, x;\n"
      "  initial begin\n"
      "    n = 8'd3;\n"
      "    x = 8'd0;\n"
      "    repeat (n) begin\n"
      "      x = x + 8'd1;\n"
      "      n = 8'd10;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(LoopStatementSim, RepeatZCountZeroIterations) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] n;\n"
      "  initial begin\n"
      "    x = 8'd42;\n"
      "    n = 8'bz;\n"
      "    repeat (n) x = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(LoopStatementSim, RepeatParameterCount) {
  // §12.7.2: the count expression may be sourced from a parameter (§11.2.1) --
  // the very form the LRM's multiplier example uses, "repeat (size)". The
  // parameter is resolved during elaboration and read once before the loop.
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  parameter size = 6;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    repeat (size) x = x + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 6u);
}

TEST(LoopStatementSim, RepeatLocalparamCount) {
  // §12.7.2: a localparam (another §11.2.1 constant form) as the repeat count
  // drives the same evaluate-once-then-iterate behaviour as a parameter.
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  localparam int cnt = 7;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    repeat (cnt) x = x + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

TEST(LoopStatementSim, RepeatCompoundCountCachedWhenOperandMutated) {
  // §12.7.2: the count expression is evaluated exactly once before the loop
  // starts, so changing *any part* of a compound count expression inside the
  // body has no effect on the iteration count. Here the count is a+b; mutating
  // operand a inside the loop must not extend the run.
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b, x;\n"
      "  initial begin\n"
      "    a = 8'd2;\n"
      "    b = 8'd1;\n"
      "    x = 8'd0;\n"
      "    repeat (a + b) begin\n"
      "      x = x + 8'd1;\n"
      "      a = 8'd50;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(LoopStatementSim, RepeatPartiallyUnknownCountZeroIterations) {
  // §12.7.2: a single unknown bit makes the whole count unknown, so it is
  // treated as zero and the body never runs. Were the known bits used instead,
  // this pattern would suggest several iterations.
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] n;\n"
      "  initial begin\n"
      "    x = 8'd42;\n"
      "    n = 8'b0000010x;\n"
      "    repeat (n) x = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(LoopStatementSim, RepeatGenvarCount) {
  // §12.7.2: the count expression may be a genvar (§11.2.1), which is admitted
  // only inside a generate scope and substituted as a per-instance constant.
  // Each unrolled instance runs its body the genvar's value of times, so the
  // element written by instance i ends at i.
  SimFixture f;
  RunModuleArray(f,
                 "module t;\n"
                 "  logic [7:0] out [0:3];\n"
                 "  generate\n"
                 "    for (genvar i = 0; i < 4; i = i + 1) begin : g\n"
                 "      initial begin\n"
                 "        out[i] = 8'd0;\n"
                 "        repeat (i) out[i] = out[i] + 8'd1;\n"
                 "      end\n"
                 "    end\n"
                 "  endgenerate\n"
                 "endmodule\n",
                 "out", {0u, 1u, 2u, 3u});
}

TEST(LoopStatementSim, RepeatConstantFunctionCallCount) {
  // §12.7.2: the count expression may be a function call (the last §11.2.1
  // constant form), which takes the call-evaluation path rather than a plain
  // variable read. The returned value is read once before the loop and drives
  // the iteration count.
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  function automatic logic [7:0] three();\n"
      "    three = 8'd3;\n"
      "  endfunction\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    repeat (three()) x = x + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

// §12.7.2's own shift-add multiplier, run as a function body (§13.4): the
// loop runs `size` times inside the call, so 13 * 17 is 221 where a body that
// skipped the loop returned 0. The widths are written as literals, the
// example's `longsize` and `size` standing for 16 and 8.
TEST(LoopStatementSim, RepeatInsideAFunctionRunsItsCount) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  parameter size = 8;\n"
      "  function logic [16:1] mult(logic [8:1] opa, logic [8:1] opb);\n"
      "    logic [16:1] shift_opa, shift_opb, result;\n"
      "    shift_opa = opa; shift_opb = opb; result = 0;\n"
      "    repeat (size) begin\n"
      "      if (shift_opb[1]) result = result + shift_opa;\n"
      "      shift_opa = shift_opa << 1;\n"
      "      shift_opb = shift_opb >> 1;\n"
      "    end\n"
      "    return result;\n"
      "  endfunction\n"
      "  logic [15:0] x;\n"
      "  initial x = mult(13, 17);\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 221u);
}

// A class method's body runs a repeat on its argument's count as a module
// function's does.
TEST(LoopStatementSim, RepeatInsideAClassMethodRunsItsCount) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "class R;\n"
      "  int acc;\n"
      "  function int m(int n, int v);\n"
      "    acc = 0;\n"
      "    repeat (n) acc += v;\n"
      "    return acc;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  R r;\n"
      "  int x;\n"
      "  initial begin r = new; x = r.m(3, 10); end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

// §12.8: a break ends a repeat in a function body before its count runs out.
TEST(LoopStatementSim, BreakEndsARepeatInsideAFunction) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  function int f();\n"
      "    int r;\n"
      "    r = 0;\n"
      "    repeat (100) begin r++; if (r == 5) break; end\n"
      "    return r;\n"
      "  endfunction\n"
      "  int x;\n"
      "  initial x = f();\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

// §12.8: a continue skips the rest of the body and the repeat goes on to its
// next iteration, so the count still runs out and the assignment after the
// continue is never reached.
TEST(LoopStatementSim, ContinueInARepeatInsideAFunctionGoesOn) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  function int f();\n"
      "    int r;\n"
      "    r = 0;\n"
      "    repeat (4) begin r++; continue; r = 100; end\n"
      "    return r;\n"
      "  endfunction\n"
      "  int x;\n"
      "  initial x = f();\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

// §12.7.2: a negative count of a signed expression runs the body no times in a
// function body as it does in a process; read as unsigned, -1 would run it
// more than four billion times.
TEST(LoopStatementSim, NegativeRepeatCountInsideAFunctionRunsNoTimes) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  function int f(int n);\n"
      "    int r;\n"
      "    r = 7;\n"
      "    repeat (n) r++;\n"
      "    return r;\n"
      "  endfunction\n"
      "  int x;\n"
      "  initial x = f(-1);\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

}  // namespace
