#include <gtest/gtest.h>

#include <utility>

#include "helpers_precedence_rhs.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/operator_binding_power.h"

using namespace delta;
namespace {

TEST(Precedence, ShiftLowerThanAdd) {
  auto* rhs = ParsePrecedenceRhs(
      "module t;\n"
      "  initial x = a + b << c;\n"
      "endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kLtLt);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kPlus);
}

TEST(Precedence, LogicalAndHigherThanOr) {
  auto* rhs = ParsePrecedenceRhs(
      "module t;\n"
      "  initial x = a && b || c;\n"
      "endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kPipePipe);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kAmpAmp);
}

TEST(Precedence, ShiftHigherThanComparison) {
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a < b << c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kLt);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->rhs->op, TokenKind::kLtLt);
}

TEST(Precedence, EqualityHigherThanBitwiseAnd) {
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a & b == c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kAmp);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->rhs->op, TokenKind::kEqEq);
}

TEST(Precedence, BitwiseOrHigherThanLogicalAndOnRight) {
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a && b | c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kAmpAmp);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->rhs->op, TokenKind::kPipe);
}

TEST(Precedence, UnaryHigherThanBinary) {
  auto* rhs = ParsePrecedenceRhs("module m; initial x = ~a & b; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kAmp);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kTilde);
}

TEST(Precedence, LogicalOrHigherThanTernary) {
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a || b ? c : d; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->condition, nullptr);
  EXPECT_EQ(rhs->condition->op, TokenKind::kPipePipe);
}

TEST(Precedence, TernaryHigherThanImplication) {
  auto* rhs = ParsePrecedenceRhs(
      "module m;\n"
      "  logic a, b, c, d, e;\n"
      "  initial e = a -> b ? c : d;\n"
      "endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kArrow);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kTernary);
}

TEST(Precedence, ImplicationAfterTernaryTakesTheTernary) {
  auto* rhs = ParsePrecedenceRhs(
      "module m;\n"
      "  logic a, b, c, d, e;\n"
      "  initial e = a ? b : c -> d;\n"
      "endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kArrow);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->lhs->false_expr, nullptr);
  EXPECT_EQ(rhs->lhs->false_expr->kind, ExprKind::kIdentifier);
}

TEST(Precedence, EquivalenceAfterTernaryTakesTheTernary) {
  auto* rhs = ParsePrecedenceRhs(
      "module m;\n"
      "  logic a, b, c, d, e;\n"
      "  initial e = a ? b : c <-> d;\n"
      "endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kLtDashGt);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kTernary);
}

TEST(Precedence, TernaryFalseExpressionNestsToTheRight) {
  auto* rhs = ParsePrecedenceRhs(
      "module m;\n"
      "  logic a, b, c, d, e, f, g;\n"
      "  initial g = a ? b : c ? d : e || f;\n"
      "endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->false_expr->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->false_expr->op, TokenKind::kPipePipe);
}

TEST(Precedence, ArithShiftSamePrecedenceAsLogicShift) {
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a <<< b >> c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kGtGt);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kLtLtLt);
}

TEST(Precedence, MultiplyLeftAssoc) {
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a * b / c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kSlash);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kStar);
}

TEST(Precedence, ModulusSamePrecedenceAsMultiply) {
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a % b * c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kStar);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kPercent);
}

TEST(Precedence, AllPrecedenceLevelsInOneExpression) {
  auto* rhs = ParsePrecedenceRhs(
      "module m;\n"
      "  initial x = a || b && c | d ^ e & f == g < h << i + j * k;\n"
      "endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kPipePipe);
}

TEST(OperatorBindingPower, HigherRowsBindTighter) {
  EXPECT_GT(InfixBindingPower(TokenKind::kStar).first,
            InfixBindingPower(TokenKind::kPlus).first);
  EXPECT_GT(InfixBindingPower(TokenKind::kPower).first,
            InfixBindingPower(TokenKind::kStar).first);
  EXPECT_GT(InfixBindingPower(TokenKind::kAmpAmp).first,
            InfixBindingPower(TokenKind::kPipePipe).first);
}

TEST(OperatorBindingPower, UnaryOperatorsBindTightest) {
  EXPECT_GT(PrefixBindingPower(TokenKind::kMinus),
            InfixBindingPower(TokenKind::kPower).second);
}

TEST(OperatorBindingPower, AssociativityFollowsTheTable) {
  const auto kImplies = InfixBindingPower(TokenKind::kArrow);
  EXPECT_GT(kImplies.first, kImplies.second);
  const auto kPlus = InfixBindingPower(TokenKind::kPlus);
  EXPECT_LT(kPlus.first, kPlus.second);
}

TEST(OperatorBindingPower, ANonOperatorHasNone) {
  EXPECT_EQ(InfixBindingPower(TokenKind::kSemicolon).first, -1);
  EXPECT_EQ(PrefixBindingPower(TokenKind::kStar), -1);
}

}  // namespace
