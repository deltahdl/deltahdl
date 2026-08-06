

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

// §28.3.5: a [lhi:rhi] range on a module instance name yields abs(lhi-rhi)+1
// distinct instances, the same array-of-instances rule that governs gates.
TEST(ModuleInstanceArrayElaboration, RangeExpandsToInstanceCount) {
  ElabFixture f;
  auto* design = Elaborate(
      "module child; endmodule\n"
      "module top;\n"
      "  child c0 [3:0] ();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->children.size(), 4u);
}

// §28.3.5: one instance identifier may be associated with only one range;
// reusing `u` for a second array is an illegal redeclaration.
TEST(ModuleInstanceArrayElaboration, ReusedArrayInstanceNameRejected) {
  ElabFixture f;
  Elaborate(
      "module child; endmodule\n"
      "module top;\n"
      "  child u [0:3] ();\n"
      "  child u [4:7] ();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

// §28.3.5: the range bounds are constant expressions (§11.2.1). End-to-end: a
// parameter bound [N:0] with N=3 yields abs(N-0)+1 = 4 instances.
TEST(ModuleInstanceArrayElaboration, ParameterBoundExpandsToInstanceCount) {
  ElabFixture f;
  auto* design = Elaborate(
      "module child; endmodule\n"
      "module top;\n"
      "  parameter int N = 3;\n"
      "  child c0 [N:0] ();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->children.size(), 4u);
}

// §28.3.5 (negative): a range bound that is not a constant expression (a
// variable) is rejected.
TEST(ModuleInstanceArrayElaboration, NonConstantRangeBoundRejected) {
  ElabFixture f;
  Elaborate(
      "module child; endmodule\n"
      "module top;\n"
      "  reg [3:0] r;\n"
      "  child c0 [r:0] ();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
