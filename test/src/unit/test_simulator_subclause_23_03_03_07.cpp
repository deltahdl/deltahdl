#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(DissimilarNetTypePortConnectionSimulation,
     ValuePropagatesThroughPortWhenInternalDominates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(output wand a);\n"
      "  assign a = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(DissimilarNetTypePortConnectionSimulation,
     ValuePropagatesThroughPortWhenExternalDominates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(output wire a);\n"
      "  assign a = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  wand w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(DissimilarNetTypePortConnectionSimulation,
     ValuePropagatesWhenNeitherNetDominatesExternalUsed) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(output wand a);\n"
      "  assign a = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  trireg w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(DissimilarNetTypePortConnectionSimulation,
     TriregDominatingPortPropagatesValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(output trireg a);\n"
      "  assign a = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(DissimilarNetTypePortConnectionSimulation,
     InoutPortDissimilarNetTypesPropagatesValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(inout wand a);\n"
      "  assign a = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(DissimilarNetTypePortConnectionSimulation,
     InputPortDissimilarNetTypesPropagatesValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(input wand a, output wire b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  wire r;\n"
      "  assign w = 1'b1;\n"
      "  child u(.a(w), .b(r));\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(GenerateBlockInoutConnectionSim, AnInoutReachesTheNetItsBlockDeclares) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child(inout wire p);\n"
                       "  assign p = 1'b1;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  if (1) begin : g\n"
                       "    wire n;\n"
                       "    child c(.p(n));\n"
                       "  end\n"
                       "  initial #1 $display(\"g.n %b\", g.n);\n"
                       "endmodule\n",
                       f),
            "g.n 1\n");
}

TEST(GenerateBlockInoutConnectionSim, TheBlocksNetStandsOverTheModules) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child(inout wire p);\n"
                       "  assign p = 1'b1;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  wire n;\n"
                       "  if (1) begin : g\n"
                       "    wire n;\n"
                       "    child c(.p(n));\n"
                       "  end\n"
                       "  initial #1 $display(\"g.n %b n %b\", g.n, n);\n"
                       "endmodule\n",
                       f),
            "g.n 1 n z\n");
}

TEST(GenerateBlockInoutConnectionSim, ANameTheBlockLacksIsTheModulesNet) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child(inout wire p);\n"
                       "  assign p = 1'b1;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  wire n;\n"
                       "  if (1) begin : g\n"
                       "    wire m;\n"
                       "    child c(.p(n));\n"
                       "  end\n"
                       "  initial #1 $display(\"n %b\", n);\n"
                       "endmodule\n",
                       f),
            "n 1\n");
}

}  // namespace
