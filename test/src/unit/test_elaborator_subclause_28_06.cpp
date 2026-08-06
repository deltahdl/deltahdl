

#include "fixture_elaborator.h"
#include "helpers_gate_elab.h"

using namespace delta;

namespace {

TEST(TristateGateElaboration, OutputIsFirstTerminal) {
  ElabFixture f;
  const auto* assign = ElaborateSingleGateAssign("bufif1 b1(y, a, en);", f);
  ASSERT_NE(assign, nullptr);
  ASSERT_NE(assign->lhs, nullptr);
  EXPECT_EQ(assign->lhs->text, "y");
}

TEST(TristateGateElaboration, Bufif1LowersToTernaryWithZOnBlocked) {
  // bufif1 conducts on control (terminal 3), passing the data input (terminal
  // 2) and driving Z when blocked. The data arm is doubly negated so a
  // high-impedance data value folds to x per Table 28-5 without inverting a
  // 0 or 1.
  ElabFixture f;
  const auto* rhs = ElaborateSingleGateRhs("bufif1 b1(y, a, en);", f);
  ASSERT_NE(rhs, nullptr);
  ASSERT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->condition, nullptr);
  EXPECT_EQ(rhs->condition->text, "en");
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->true_expr->op, TokenKind::kTilde);
  ASSERT_NE(rhs->true_expr->lhs, nullptr);
  EXPECT_EQ(rhs->true_expr->lhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->true_expr->lhs->op, TokenKind::kTilde);
  ASSERT_NE(rhs->true_expr->lhs->lhs, nullptr);
  EXPECT_EQ(rhs->true_expr->lhs->lhs->text, "a");
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kUnbasedUnsizedLiteral);
}

TEST(TristateGateElaboration, Bufif0LowersToTernaryWithZOnActiveControl) {
  // bufif0 conducts when control is 0, so Z is on the true arm and the data
  // input is on the false arm -- doubly negated so a high-impedance data value
  // folds to x per Table 28-5.
  ElabFixture f;
  const auto* rhs = ElaborateSingleGateRhs("bufif0 b1(y, a, en);", f);
  ASSERT_NE(rhs, nullptr);
  ASSERT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kUnbasedUnsizedLiteral);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->false_expr->op, TokenKind::kTilde);
  ASSERT_NE(rhs->false_expr->lhs, nullptr);
  EXPECT_EQ(rhs->false_expr->lhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->false_expr->lhs->op, TokenKind::kTilde);
  ASSERT_NE(rhs->false_expr->lhs->lhs, nullptr);
  EXPECT_EQ(rhs->false_expr->lhs->lhs->text, "a");
}

TEST(TristateGateElaboration, Notif1InvertsDataArm) {
  ElabFixture f;
  const auto* rhs = ElaborateSingleGateRhs("notif1 n1(y, a, en);", f);
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
  const auto* rhs = ElaborateSingleGateRhs("notif0 n1(y, a, en);", f);
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
