

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(MosSwitchElaboration, OutputIsFirstTerminal) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire y, a, en;\n"
      "  nmos n1(y, a, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  ASSERT_NE(mod->assigns[0].lhs, nullptr);
  EXPECT_EQ(mod->assigns[0].lhs->text, "y");
}

TEST(MosSwitchElaboration, NmosLowersToTernaryWithZOnBlocked) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire y, a, en;\n"
      "  nmos n1(y, a, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  auto* rhs = mod->assigns[0].rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->condition, nullptr);
  EXPECT_EQ(rhs->condition->text, "en");
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->true_expr->text, "a");
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kUnbasedUnsizedLiteral);
}

TEST(MosSwitchElaboration, PmosLowersToTernaryWithZOnActiveControl) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire y, a, en;\n"
      "  pmos p1(y, a, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  auto* rhs = mod->assigns[0].rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kUnbasedUnsizedLiteral);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->false_expr->text, "a");
}

TEST(MosSwitchElaboration, RnmosConductsOnOneWithoutInverting) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire y, a, en;\n"
      "  rnmos r1(y, a, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  auto* rhs = mod->assigns[0].rhs;
  ASSERT_NE(rhs, nullptr);
  ASSERT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->true_expr->text, "a");
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kUnbasedUnsizedLiteral);
}

TEST(MosSwitchElaboration, RpmosConductsOnZeroWithoutInverting) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire y, a, en;\n"
      "  rpmos r1(y, a, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  auto* rhs = mod->assigns[0].rhs;
  ASSERT_NE(rhs, nullptr);
  ASSERT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kUnbasedUnsizedLiteral);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->false_expr->text, "a");
}

}  // namespace
