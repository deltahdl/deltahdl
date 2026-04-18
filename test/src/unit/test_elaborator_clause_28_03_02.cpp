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

TEST(GateStrengthValidity, BothHighzStrengthsInvalid) {
  EXPECT_FALSE(ValidateStrengthSpec(StrengthLvl::kHighz, StrengthLvl::kHighz,
                                    GateType::kAnd));
}

TEST(GateStrengthValidity, DefaultStrengthIsStrong) {
  GateDeclInfo info;
  info.has_strength = false;
  EXPECT_TRUE(ValidateGateDecl(info));
}

// --- Gate with strength elaborates normally ---
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

// (highz0, highz1) is an invalid combination regardless of the site where
// the strength spec appears, including gate instances.
TEST(GateStrengthValidity, GateInst_Highz0Highz1Rejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire a, b, y;\n"
      "  and (highz0, highz1) g1(y, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// The reversed-order form of the same forbidden pair must also be rejected.
TEST(GateStrengthValidity, GateInst_Highz1Highz0Rejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire a, b, y;\n"
      "  and (highz1, highz0) g1(y, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
