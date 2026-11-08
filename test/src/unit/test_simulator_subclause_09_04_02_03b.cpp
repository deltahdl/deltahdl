#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ConditionalEventIffSim, IffConditionSetAboveLow64BitsFires) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk;\n"
      "  logic [64:0] enable;\n"
      "  logic [31:0] count;\n"
      "  initial begin\n"
      "    clk = 0; enable = 0; count = 0;\n"
      "    enable[64] = 1'b1;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge clk iff enable)\n"
      "    count = count + 1;\n"
      "endmodule\n",
      f, "count");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ConditionalEventIffSim, IffMultiBitGuardWithLowBitClearFires) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] enable;\n"
      "  logic [31:0] count;\n"
      "  initial begin\n"
      "    clk = 0; enable = 8'hFE; count = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge clk iff enable)\n"
      "    count = count + 1;\n"
      "endmodule\n",
      f, "count");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ConditionalEventIffSim, IffConditionHighImpedanceSuppresses) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk;\n"
      "  logic enable;\n"
      "  logic [31:0] count;\n"
      "  initial begin\n"
      "    clk = 0; enable = 1'bz; count = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge clk iff enable)\n"
      "    count = count + 1;\n"
      "endmodule\n",
      f, "count");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(ConditionalEventIffSim, IffOnNamedEventFalseSuppresses) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event e;\n"
      "  logic en;\n"
      "  logic [31:0] count;\n"
      "  initial begin\n"
      "    en = 0; count = 0;\n"
      "  end\n"
      "  initial begin\n"
      "    @(e iff en);\n"
      "    count = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 -> e;\n"
      "    #1 -> e;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "count");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(ConditionalEventIffSim, IffOnNamedEventTrueResumes) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  event e;\n"
      "  logic en;\n"
      "  logic [31:0] count;\n"
      "  initial begin\n"
      "    en = 1; count = 0;\n"
      "  end\n"
      "  initial begin\n"
      "    @(e iff en);\n"
      "    count = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 -> e;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "count");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ConditionalEventIffSim, IffGuardsOnlyItsOwnOperandOfAnOrList) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic a, b, c;\n"
      "  logic [31:0] count;\n"
      "  initial begin\n"
      "    a = 0; b = 0; c = 0;\n"
      "    #1 count = 0;\n"
      "    #1 a = 1;\n"
      "    #1 b = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(a iff c or b)\n"
      "    count = count + 1;\n"
      "endmodule\n",
      f, "count");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(ConditionalEventIffSim, ProceduralEventControlIffFalseKeepsWaiting) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk, en;\n"
      "  logic [31:0] count;\n"
      "  initial begin\n"
      "    clk = 0; en = 0; count = 0;\n"
      "  end\n"
      "  initial begin\n"
      "    @(posedge clk iff en);\n"
      "    count = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 clk = 1;\n"
      "    #1 clk = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "count");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(ConditionalEventIffSim, ProceduralEventControlIffTrueResumes) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic clk, en;\n"
      "  logic [31:0] count;\n"
      "  initial begin\n"
      "    clk = 0; en = 1; count = 0;\n"
      "  end\n"
      "  initial begin\n"
      "    @(posedge clk iff en);\n"
      "    count = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "count");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

}  // namespace
