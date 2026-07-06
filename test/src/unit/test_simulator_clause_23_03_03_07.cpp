
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(DissimilarNetTypePortConnectionSimulation,
     ValuePropagatesThroughPortWhenInternalDominates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(output wand a);\n"
      "  assign a = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(DissimilarNetTypePortConnectionSimulation,
     ValuePropagatesThroughPortWhenExternalDominates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(output wire a);\n"
      "  assign a = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  wand w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(DissimilarNetTypePortConnectionSimulation,
     ValuePropagatesWhenNeitherNetDominatesExternalUsed) {
  // wand (internal) and trireg (external) have no dominating relationship, so
  // the external net type is used for the collapsed net; the driven value
  // still propagates across the merged net.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(output wand a);\n"
      "  assign a = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  trireg w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(DissimilarNetTypePortConnectionSimulation,
     TriregDominatingPortPropagatesValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(output trireg a);\n"
      "  assign a = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("w");
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
  auto* design = ElaborateSrc(
      "module child(inout wand a);\n"
      "  assign a = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  child u(.a(w));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §23.3.3.7: a value supplied to a dissimilar-net-type input port crosses the
// collapsed net into the child, which forwards it to a same-type output whose
// connected net is observed. Exercises the input port position of the collapse.
TEST(DissimilarNetTypePortConnectionSimulation,
     InputPortDissimilarNetTypesPropagatesValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input wand a, output wire b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  wire r;\n"
      "  assign w = 1'b1;\n"
      "  child u(.a(w), .b(r));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

}  // namespace
