#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_precedence_rhs.h"

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
  // Division and modulus share a Table 11-2 row, so neither binds tighter than
  // the other; they evaluate left to right, nesting the divide under the mod.
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
  // Equivalence associates right to left: the trailing operand nests on the
  // right rather than folding the left pair first.
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
  // The conditional operator associates right to left, so the trailing
  // conditional nests inside the false branch rather than the condition.
  EXPECT_EQ(rhs->condition->kind, ExprKind::kIdentifier);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kTernary);
}

TEST(Precedence, PowerLeftAssoc) {
  // Exponentiation is a single precedence row and, like the other binary
  // operators, associates left to right; the left pair folds first.
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a ** b ** c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kPower);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kPower);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kIdentifier);
}

TEST(Precedence, UnaryBindsTighterThanBinary) {
  // Unary operators sit above every binary operator in the precedence table,
  // so the negation applies to its single operand before the bitwise AND.
  auto* rhs = ParsePrecedenceRhs("module m; initial x = ~a & b; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kAmp);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kTilde);
}

}  // namespace
