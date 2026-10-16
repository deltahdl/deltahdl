
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
  // wand (internal) and trireg (external) have no dominating relationship, so
  // the external net type is used for the collapsed net; the driven value
  // still propagates across the merged net.
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

// §23.3.3.7: an inout connection between dissimilar net types collapses the
// child port net and the parent net into a single simulated net (shared
// storage), so a value driven inside the child is observed on the connected
// parent net. Exercises the inout port position (the existing cases drive
// through output ports).
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

// §23.3.3.7: a value supplied to a dissimilar-net-type input port crosses the
// collapsed net into the child, which forwards it to a same-type output whose
// connected net is observed. Exercises the input port position of the collapse.
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

// §23.3.3.7 with §27.5 and §23.9: an inout port connected inside a generate
// block to a net the block declares is one net with that net, found under the
// block's name: c drives 1 on its port, and g.n reads it. Joined under the
// module's name alone, the port reached no net and g.n stayed z.
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

// The block's n stands over the module's n of the same name (§23.9), so the
// port is joined to the block's and the module's stays undriven at z. Joined
// under the module's name alone, the two read the other way round.
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

// Where the block declares nothing of the connection's name, the name is the
// module's (§23.9 climbing out of the block): c drives 1 on its port in g, and
// the module's n reads it.
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
