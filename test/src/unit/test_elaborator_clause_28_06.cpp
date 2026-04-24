// §28.6

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §28.6: the first terminal is the driven output and must appear as the
// lhs of the emitted continuous assign.
TEST(TristateGateElaboration, OutputIsFirstTerminal) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire y, a, en;\n"
      "  bufif1 b1(y, a, en);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  ASSERT_NE(mod->assigns[0].lhs, nullptr);
  EXPECT_EQ(mod->assigns[0].lhs->text, "y");
}

// §28.6: bufif1 conducts when control is 1 — true arm passes data, false
// arm is high-Z.
TEST(TristateGateElaboration, Bufif1LowersToTernaryWithZOnBlocked) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire y, a, en;\n"
      "  bufif1 b1(y, a, en);\n"
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

// §28.6: bufif0 conducts when control is 0 — arms are swapped relative to
// bufif1.
TEST(TristateGateElaboration, Bufif0LowersToTernaryWithZOnActiveControl) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire y, a, en;\n"
      "  bufif0 b1(y, a, en);\n"
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

// §28.6: notif gates invert the data leg; the Z leg is unchanged.
TEST(TristateGateElaboration, Notif1InvertsDataArm) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire y, a, en;\n"
      "  notif1 n1(y, a, en);\n"
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
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->true_expr->op, TokenKind::kTilde);
  ASSERT_NE(rhs->true_expr->lhs, nullptr);
  EXPECT_EQ(rhs->true_expr->lhs->text, "a");
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kUnbasedUnsizedLiteral);
}

TEST(TristateGateElaboration, Notif0InvertsDataArmAndSwapsArms) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  wire y, a, en;\n"
      "  notif0 n1(y, a, en);\n"
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
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->false_expr->op, TokenKind::kTilde);
  ASSERT_NE(rhs->false_expr->lhs, nullptr);
  EXPECT_EQ(rhs->false_expr->lhs->text, "a");
}

}  // namespace
