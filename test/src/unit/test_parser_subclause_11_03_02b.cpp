#include <gtest/gtest.h>

#include "helpers_precedence_rhs.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"

using namespace delta;
namespace {

TEST(Precedence, NestedParenthesizedExpression) {
  auto* rhs = ParsePrecedenceRhs(
      "module t;\n"
      "  initial x = ((a + b) * (c - d));\n"
      "endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kStar);
}

TEST(Precedence, ChainedAdditiveLeftAssoc) {
  auto* rhs = ParsePrecedenceRhs(
      "module t;\n"
      "  initial x = a + b - c + d;\n"
      "endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
}

TEST(Precedence, MultiplyHigherThanAdd) {
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a + b * c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);

  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->rhs->op, TokenKind::kStar);
}

TEST(Precedence, ChainedBinaryOps) {
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a | b & c ^ d; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
}

TEST(Precedence, ParenthesizedExpr) {
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = (a + b) * c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kStar);

  EXPECT_EQ(rhs->lhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kPlus);
}

TEST(Precedence, ParenthesesOverrideBitwise) {
  auto* rhs = ParsePrecedenceRhs(
      "module t;\n"
      "  initial x = (a | b) & c;\n"
      "endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kAmp);
}

TEST(Precedence, ImplicationRightAssocStructure) {
  auto* rhs = ParsePrecedenceRhs(
      "module t;\n"
      "  logic a, b, c, d;\n"
      "  initial d = a -> b -> c;\n"
      "endmodule\n");
  ASSERT_NE(rhs, nullptr);

  EXPECT_EQ(rhs->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->rhs->op, TokenKind::kArrow);
}

TEST(Precedence, CompareAndLogicalWithParentheses) {
  auto* rhs = ParsePrecedenceRhs(
      "module t;\n"
      "  initial x = (a > 0) && (b < 10);\n"
      "endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kAmpAmp);
}

TEST(Precedence, SameRowEqualPrecedence) {
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a / b % c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kPercent);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kSlash);
}

TEST(Precedence, EquivalenceRightAssoc) {
  auto* rhs = ParsePrecedenceRhs(
      "module t;\n"
      "  logic a, b, c, d;\n"
      "  initial d = a <-> b <-> c;\n"
      "endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kLtDashGt);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->op, TokenKind::kLtDashGt);
}

TEST(Precedence, ConditionalRightAssoc) {
  auto* rhs = ParsePrecedenceRhs(
      "module t;\n"
      "  logic a, b, c, d, e;\n"
      "  initial x = a ? b : c ? d : e;\n"
      "endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  EXPECT_EQ(rhs->condition->kind, ExprKind::kIdentifier);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kTernary);
}

TEST(Precedence, PowerLeftAssoc) {
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a ** b ** c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kPower);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kPower);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kIdentifier);
}

TEST(Precedence, RelationalHigherThanEquality) {
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a == b < c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kEqEq);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->rhs->op, TokenKind::kLt);
}

TEST(Precedence, RelationalLeftAssoc) {
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a < b < c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kLt);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kLt);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kIdentifier);
}

TEST(Precedence, PostfixSelectHigherThanUnary) {
  auto* rhs = ParsePrecedenceRhs(
      "module m;\n"
      "  logic [3:0] a;\n"
      "  initial x = ~a[0];\n"
      "endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTilde);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->lhs->base, nullptr);
  EXPECT_EQ(rhs->lhs->base->kind, ExprKind::kIdentifier);
}

TEST(Precedence, UnaryHigherThanPower) {
  auto* rhs = ParsePrecedenceRhs("module m; initial x = -a ** b; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPower);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kMinus);
}

TEST(Precedence, PowerHigherThanMultiply) {
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a * b ** c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kStar);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->op, TokenKind::kPower);
}

TEST(Precedence, AdditiveHigherThanShift) {
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a + b << c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kLtLt);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kPlus);
}

TEST(Precedence, BitwiseAndHigherThanXor) {
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a & b ^ c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kCaret);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kAmp);
}

TEST(Precedence, XorHigherThanOr) {
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a ^ b | c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kPipe);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kCaret);
}

TEST(Precedence, BitwiseOrHigherThanLogicalAnd) {
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a | b && c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kAmpAmp);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kPipe);
}

TEST(Precedence, LogicalAndHigherThanLogicalOr) {
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a && b || c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kPipePipe);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kAmpAmp);
}

TEST(Precedence, ConditionalHigherThanImplication) {
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

TEST(Precedence, ShiftLeftAssoc) {
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a << b >> c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kGtGt);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kLtLt);
}

TEST(Precedence, EqualityLeftAssoc) {
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a == b != c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kBangEq);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kEqEq);
}

TEST(Precedence, BitwiseAndLeftAssoc) {
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a & b & c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kAmp);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kAmp);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kIdentifier);
}

TEST(Precedence, BitwiseXorLeftAssoc) {
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a ^ b ^ c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kCaret);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kCaret);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kIdentifier);
}

TEST(Precedence, BitwiseOrLeftAssoc) {
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a | b | c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kPipe);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kPipe);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kIdentifier);
}

TEST(Precedence, LogicalAndLeftAssoc) {
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a && b && c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kAmpAmp);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kAmpAmp);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kIdentifier);
}

TEST(Precedence, LogicalOrLeftAssoc) {
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a || b || c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kPipePipe);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kPipePipe);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kIdentifier);
}

}  // namespace
