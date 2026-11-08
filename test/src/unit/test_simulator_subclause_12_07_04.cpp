#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(LoopStatementSim, WhileBasic) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd10;\n"
      "    while (x > 0) x = x - 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(LoopStatementSim, WhileZeroIter) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd42;\n"
      "    while (0) x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(LoopStatementSim, WhileTrueConditionRunsUntilBreak) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    while (1) begin\n"
      "      if (x == 8'd5) break;\n"
      "      x = x + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(LoopStatementSim, WhileConditionRetestedAfterContinue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x, sum;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    sum = 8'd0;\n"
      "    while (x < 8'd5) begin\n"
      "      x = x + 8'd1;\n"
      "      if (x == 8'd3) continue;\n"
      "      sum = sum + x;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "sum");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 12u);
}

TEST(LoopStatementSim, WhileBlock) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x, cnt;\n"
      "  initial begin\n"
      "    x = 8'd3;\n"
      "    cnt = 8'd0;\n"
      "    while (x > 0) begin\n"
      "      x = x - 8'd1;\n"
      "      cnt = cnt + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "cnt");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(LoopStatementSim, WhileXConditionNoIteration) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  logic cond;\n"
      "  initial begin\n"
      "    x = 8'd42;\n"
      "    cond = 1'bx;\n"
      "    while (cond) x = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(LoopStatementSim, WhileVectorConditionIteratesUntilZero) {
  SimFixture f;
  auto* count = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] tempreg;\n"
      "  logic [7:0] count;\n"
      "  initial begin\n"
      "    count = 8'd0;\n"
      "    tempreg = 8'b1011_0010;\n"
      "    while (tempreg) begin\n"
      "      if (tempreg[0]) count = count + 8'd1;\n"
      "      tempreg = tempreg >> 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "count");
  ASSERT_NE(count, nullptr);
  EXPECT_EQ(count->value.ToUint64(), 4u);
  auto* tempreg = f.ctx.FindVariable("tempreg");
  ASSERT_NE(tempreg, nullptr);
  EXPECT_EQ(tempreg->value.ToUint64(), 0u);
}

}  // namespace
