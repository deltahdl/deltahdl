#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"
#include "model_gate_declaration.h"
#include "parser/ast_expr.h"

namespace {

TEST(GateStrengthValidity, StrengthSpecAllowedForPullGates) {
  EXPECT_TRUE(CanHaveStrengthSpec(ModelGateType::kPullup));
  EXPECT_TRUE(CanHaveStrengthSpec(ModelGateType::kPulldown));
}

TEST(GateStrengthValidity, StrengthSpecDisallowedForSwitches) {
  EXPECT_FALSE(CanHaveStrengthSpec(ModelGateType::kNmos));
  EXPECT_FALSE(CanHaveStrengthSpec(ModelGateType::kPmos));
  EXPECT_FALSE(CanHaveStrengthSpec(ModelGateType::kTran));
  EXPECT_FALSE(CanHaveStrengthSpec(ModelGateType::kCmos));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "drive strength (highz0, highz1) is illegal", 3,
                            "28.3.2"));
}

TEST(GateElaboration, HighzBothStrengthsRejectedReversedOrder) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire a, b, y;\n"
      "  and (highz1, highz0) g1(y, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "drive strength (highz0, highz1) is illegal", 3,
                            "28.3.2"));
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
