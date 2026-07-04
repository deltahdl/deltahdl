#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "model_gate_declaration.h"

namespace {

TEST(GateStrengthValidity, StrengthSpecAllowedForPullGates) {
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kPullup));
  EXPECT_TRUE(CanHaveStrengthSpec(GateType::kPulldown));
}

TEST(GateStrengthValidity, StrengthSpecDisallowedForSwitches) {
  EXPECT_FALSE(CanHaveStrengthSpec(GateType::kNmos));
  EXPECT_FALSE(CanHaveStrengthSpec(GateType::kPmos));
  EXPECT_FALSE(CanHaveStrengthSpec(GateType::kTran));
  EXPECT_FALSE(CanHaveStrengthSpec(GateType::kCmos));
}

TEST(GateStrengthValidity, DefaultStrengthIsStrong) {
  GateDeclInfo info;
  info.has_strength = false;
  EXPECT_TRUE(ValidateGateDecl(info));
}

TEST(GateElaboration, GateWithStrengthStillProducesAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, y;\n"
      "  and (strong0, strong1) g1(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  auto& ca = mod->assigns.back();
  ASSERT_NE(ca.rhs, nullptr);
  EXPECT_EQ(ca.rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(ca.rhs->op, TokenKind::kAmp);
}

TEST(GateElaboration, HighzBothStrengthsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire a, b, y;\n"
      "  and (highz0, highz1) g1(y, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §28.3.2 names both (highz0, highz1) and (highz1, highz0) as invalid. Since
// the strength0/strength1 specifications may appear in either order, exercise
// the reversed (strength1-first) form to confirm the illegal-pair rule fires
// regardless of the order the keywords are written.
TEST(GateElaboration, HighzBothStrengthsRejectedReversedOrder) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire a, b, y;\n"
      "  and (highz1, highz0) g1(y, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(GateElaboration, DriveStrengthPropagatedToContAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire a, b, y;\n"
      "  and (strong0, highz1) g1(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  auto& ca = mod->assigns.back();
  EXPECT_EQ(ca.drive_strength0, 4u);
  EXPECT_EQ(ca.drive_strength1, 1u);
}

}  // namespace
