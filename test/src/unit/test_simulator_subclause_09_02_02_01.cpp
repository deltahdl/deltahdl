#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(GeneralPurposeAlwaysSimulation, ClockOscillatorWithDelay) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic [31:0] clk;\n"
      "  initial clk = 0;\n"
      "  always #5 clk = clk + 1;\n"
      "  initial #27 $finish;\n"
      "endmodule\n",
      f, "clk");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(GeneralPurposeAlwaysSimulation, RepeatsUnderParameterDelay) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  parameter half_period = 5;\n"
      "  logic [31:0] areg;\n"
      "  initial areg = 0;\n"
      "  always #half_period areg = areg + 1;\n"
      "  initial #22 $finish;\n"
      "endmodule\n",
      f, "areg");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

TEST(GeneralPurposeAlwaysSimulation, RepeatsUnderLocalparamDelay) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  localparam step = 5;\n"
      "  logic [31:0] areg;\n"
      "  initial areg = 0;\n"
      "  always #step areg = areg + 1;\n"
      "  initial #22 $finish;\n"
      "endmodule\n",
      f, "areg");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

TEST(GeneralPurposeAlwaysSimulation, TwoPhaseClockBeginEnd) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module m;\n"
      "  logic clk;\n"
      "  initial clk = 0;\n"
      "  always begin\n"
      "    #5 clk = 1;\n"
      "    #5 clk = 0;\n"
      "  end\n"
      "  initial #17 $finish;\n"
      "endmodule\n",
      f, "clk");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(GeneralPurposeAlwaysSimulation, SensitivityListTriggersOnEdge) {
  SimFixture f;
  auto* q = RunAndFindVar(
      "module m;\n"
      "  logic clk, d, q;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    d = 1;\n"
      "    q = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge clk) q = d;\n"
      "endmodule\n",
      f, "q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 1u);
}

}  // namespace
