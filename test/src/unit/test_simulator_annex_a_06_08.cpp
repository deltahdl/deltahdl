#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(LoopSyntaxSimulation, ForCompoundAssignStep) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic [7:0] total;\n"
      "  initial begin\n"
      "    total = 8'd0;\n"
      "    for (int i = 0; i < 10; i += 2)\n"
      "      total = total + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "total");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(LoopSyntaxSimulation, ForPreDecrementStep) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic [7:0] last;\n"
      "  initial begin\n"
      "    last = 8'd0;\n"
      "    for (int i = 5; i > 0; --i)\n"
      "      last = i[7:0];\n"
      "  end\n"
      "endmodule\n",
      f, "last");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(LoopSyntaxSimulation, ForPreIncrementStep) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic [7:0] total;\n"
      "  initial begin\n"
      "    total = 8'd0;\n"
      "    for (int i = 0; i < 5; ++i)\n"
      "      total = total + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "total");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(LoopSyntaxSimulation, RepeatLoop) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic [7:0] total;\n"
      "  initial begin\n"
      "    total = 8'd0;\n"
      "    repeat (3) total = total + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "total");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(LoopSyntaxSimulation, WhileLoop) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    while (x < 5) x = x + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(LoopSyntaxSimulation, DoWhileRunsAtLeastOnce) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd10;\n"
      "    do x = x + 8'd1; while (x < 5);\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 11u);
}

TEST(LoopSyntaxSimulation, ForeverWithBreak) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    forever begin\n"
      "      x = x + 8'd1;\n"
      "      if (x == 8'd7) break;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

TEST(LoopSyntaxSimulation, ForeachIteratesEachElement) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic [7:0] count;\n"
      "  int arr [0:3];\n"
      "  initial begin\n"
      "    count = 8'd0;\n"
      "    foreach (arr[i]) count = count + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "count");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

TEST(LoopSyntaxSimulation, ForMultipleInitsAndSteps) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic [7:0] total;\n"
      "  logic [7:0] i;\n"
      "  logic [7:0] j;\n"
      "  initial begin\n"
      "    total = 8'd0;\n"
      "    for (i = 0, j = 10; i < j; i = i + 1, j = j - 1)\n"
      "      total = total + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "total");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(LoopSyntaxSimulation, ForVariableOfATypeReference) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  int x, s;\n"
      "  initial begin\n"
      "    s = 0;\n"
      "    for (var type(x) i = -2; i < 1; i++) s += i;\n"
      "  end\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFFFFFFDu);
}

}  // namespace
