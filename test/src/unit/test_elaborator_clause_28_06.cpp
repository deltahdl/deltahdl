

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
  ElabFixture f;
  ExpectConductsAOnEnableElseZ("bufif1 b1(y, a, en);", f);
}

TEST(TristateGateElaboration, Bufif0LowersToTernaryWithZOnActiveControl) {
  ElabFixture f;
  ExpectZOnTrueArmConductsAOnFalseArm("bufif0 b1(y, a, en);", f);
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
