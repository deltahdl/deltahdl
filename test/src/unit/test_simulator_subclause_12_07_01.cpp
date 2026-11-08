#include <gtest/gtest.h>

#include <string>

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
      "    for (int i = seed, int turns = 0; turns < 2; turns = turns + 1)\n"
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

TEST(LoopStatementSim, ForHeaderLocalInASubroutineTakesItsDeclaredWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] seed;\n"
      "  int result;\n"
      "  function void sweep();\n"
      "    for (int i = seed, int turns = 0; turns < 1; turns = turns + 1)\n"
      "      result = $bits(i);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    seed = 8'h01;\n"
      "    sweep();\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 32u);
}

TEST(LoopStatementSim,
     ForHeaderLocalInASubroutineDropsItsInitializersUnknowns) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] seed;\n"
      "  int result;\n"
      "  function void sweep();\n"
      "    for (int i = seed, int turns = 0; turns < 1; turns = turns + 1)\n"
      "      result = $isunknown(i);\n"
      "  endfunction\n"
      "  initial begin\n"
      "    seed = 8'b1x0z0000;\n"
      "    sweep();\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(LoopStatementSim, ForHeaderLocalInABlockDropsItsInitializersUnknowns) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] seed;\n"
      "  int result;\n"
      "  initial begin\n"
      "    seed = 8'b1x0z0000;\n"
      "    for (int i = seed, int turns = 0; turns < 1; turns = turns + 1)\n"
      "      result = $isunknown(i);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(LoopStatementSim, ForSeveralDeclaratorsAfterOneDataType) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    automatic int sum = 0, last = -1;\n"
      "    automatic int offset = 10, pairs = 0, jend;\n"
      "    for (int count = 0, done = 0, j = 0; j * count < 125;\n"
      "         j++, count++) begin\n"
      "      sum += j; last = j;\n"
      "    end\n"
      "    $display(\"sum=%0d last=%0d\", sum, last);\n"
      "    for (int i = 0, j = i + offset; i < 3; i++, j++) begin\n"
      "      pairs++; jend = j;\n"
      "    end\n"
      "    $display(\"pairs=%0d j_end=%0d\", pairs, jend);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "sum=66 last=11\npairs=3 j_end=12\n");
}

TEST(LoopStatementSim, ForWithoutExpressionRunsInFunctionBody) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  int g, h, k;\n"
      "  function void f();\n"
      "    for (int i = 0; ; i++) begin g = i; if (i == 3) return; end\n"
      "  endfunction\n"
      "  function void f2();\n"
      "    for (int i = 0; ; i++) begin h = i; if (i == 3) break; end\n"
      "  endfunction\n"
      "  function int f3();\n"
      "    for (int i = 0; ; i++) begin k = i; if (i == 3) return 7; end\n"
      "    return 0;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    f(); f2();\n"
      "    $display(\"g=%0d h=%0d r=%0d k=%0d\", g, h, f3(), k);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "g=3 h=3 r=7 k=3\n");
}

TEST(LoopStatementSim, ForInitWithPackageScopedTypeRuns) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "package pkg; typedef int word_t; endpackage\n"
      "module t;\n"
      "  int n = 0;\n"
      "  initial for (pkg::word_t i = 0; i < 4; i++) n++;\n"
      "endmodule\n",
      f, "n");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

TEST(LoopStatementSim, ForRealControlVariableIsReal) {
  EXPECT_EQ(
      RunAndGet("module t;\n"
                "  int n = 0;\n"
                "  initial\n"
                "    for (real r = 0.0; r < 1.0 && n < 10; r = r + 0.25)\n"
                "      n++;\n"
                "endmodule\n",
                "n"),
      4u);
}

TEST(LoopStatementSim, ForStringAndRealControlVariablesInAFunction) {
  EXPECT_EQ(
      RunAndGet("module t;\n"
                "  int n;\n"
                "  function automatic int f();\n"
                "    int c = 0;\n"
                "    for (string s = \"\"; s != \"xxx\" && c < 10;\n"
                "         s = {s, \"x\"})\n"
                "      c++;\n"
                "    for (real r = 0.0; r < 1.0 && c < 100; r = r + 0.25)\n"
                "      c += 10;\n"
                "    return c;\n"
                "  endfunction\n"
                "  initial n = f();\n"
                "endmodule\n",
                "n"),
      43u);
}

}  // namespace
