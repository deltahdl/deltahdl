

#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "model_gate_declaration.h"

namespace {

TEST(GateDecl, ArraySizeComputation) {
  EXPECT_EQ(ComputeArraySize(0, 3), 4u);
  EXPECT_EQ(ComputeArraySize(3, 0), 4u);
  EXPECT_EQ(ComputeArraySize(1, 4), 4u);
}

TEST(GateDecl, EqualRangeBoundsOneInstance) {
  EXPECT_EQ(ComputeArraySize(5, 5), 1u);
}

TEST(GateDecl, NoRangeSingleInstance) {
  GateDeclInfo info;
  info.has_range = false;
  info.has_name = true;
  info.terminal_count = 3;
  EXPECT_TRUE(ValidateGateDecl(info));
}

TEST(GateArrayElaboration, AbsBoundsFormulaWithNonZeroBounds) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire o, a, b;\n"
      "  and g[3:7](o, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(GateArrayElaboration, EqualBoundsSingleInstance) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire o, a, b;\n"
      "  and g[5:5](o, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(GateArrayElaboration, NoRangeSingleInstanceProducesOneAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire o, a, b;\n"
      "  and g1(o, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->assigns.size(), 1u);
}

TEST(GateArrayElaboration, ReversedBoundsAcceptedByElaborator) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire o, a, b;\n"
      "  and g[7:0](o, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(GateArrayElaboration, ArrayWidthTerminalConnectsPerInstance) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire [4:0] o;\n"
      "  wire [4:0] a;\n"
      "  wire [4:0] b;\n"
      "  and g[3:7](o, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(GateArrayElaboration, NonConstantRangeBoundIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire o, a, b;\n"
      "  reg [3:0] r;\n"
      "  and g[r:0](o, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(GateArrayElaboration, ParameterTypedRangeBoundIsAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter N = 7;\n"
      "  wire o, a, b;\n"
      "  and g[0:N](o, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
