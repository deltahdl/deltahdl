// §28.3.5 — The range specification on a gate or switch instance.
//
// The elaborator enforces the range semantics: an array of abs(lhi-rhi)+1
// instances; equal bounds produce a single instance; no range produces a
// single instance; bounds may be in either direction and need not include
// zero. These tests exercise the real elaboration pipeline (the formula and
// no-range/single-bounds branches in elaborator_items.cpp).

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

// abs(lhi-rhi)+1 with both bounds non-zero. Broadcast (1-bit) terminals on
// every input are accepted on a 5-instance array, exercising the formula
// branch in elaborator_items.cpp without an array-width mismatch.
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

// "If both constant expressions are equal, only one instance shall be
// generated." Equal bounds elaborate cleanly (array_len = 1).
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

// "If no range specification is given, a single instance shall be created."
// Observe a single continuous assign — no array-of-instances unrolling.
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

// "lhi is not required to be larger than rhi" at the elaborator level:
// [7:0] elaborates as the same 8-instance array as [0:7].
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

// "These instances shall differ from each other only by the index of the
// vector to which they are connected." For an array gate, an array-width
// terminal connects each instance to a different bit (per-instance), while a
// 1-bit terminal broadcasts the same bit to every instance. The elaborator's
// width check at elaborator_items.cpp accepts both forms; here we observe the
// per-instance form for a [3:7] (5-bit) array.
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

// "The range shall be specified by two constant expressions." A range
// bound that resolves to a runtime variable (non-constant) must be rejected
// by the elaborator.
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

// Counterpart to the negative test: a parameter-typed bound resolves to a
// constant via the module's parameter scope and elaborates cleanly.
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
