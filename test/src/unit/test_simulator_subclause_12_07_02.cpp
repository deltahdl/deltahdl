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

TEST(LoopStatementSim, RepeatRealCountRoundsToAnInteger) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  real r = 2.6;\n"
      "  int n = 0;\n"
      "  initial begin\n"
      "    repeat (r) n++;\n"
      "    repeat (-1.0) n += 100;\n"
      "  end\n"
      "endmodule\n",
      f, "n");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(LoopStatementSim, RepeatCountAbove64BitsIsNotCutToItsLowWord) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int n = 0;\n"
      "  initial repeat (65'h1_0000_0000_0000_0003) #1 n++;\n"
      "  initial #10 $finish;\n"
      "endmodule\n",
      f, "n");
  ASSERT_NE(var, nullptr);
  EXPECT_GT(var->value.ToUint64(), 3u);
}

}  // namespace
