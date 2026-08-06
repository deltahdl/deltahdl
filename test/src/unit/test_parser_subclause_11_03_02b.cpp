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

TEST(Precedence, RelationalHigherThanEquality) {
  // The relational row sits one tier above the equality row, so the comparison
  // folds into the right operand of the equality rather than the other way
  // around.
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
  // Relational operators share one precedence row and associate left to right,
  // so the leading pair folds first.
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a < b < c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kLt);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kLt);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kIdentifier);
}

TEST(Precedence, PostfixSelectHigherThanUnary) {
  // The parenthesis/select/member/scope tier is the highest-precedence row,
  // sitting above the unary operators. A bit-select therefore binds to its
  // operand before the unary negation applies: the select nests as the unary's
  // operand rather than the unary nesting inside the select's base.
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
  // Unary operators occupy the tier directly above exponentiation, so the unary
  // minus applies to its operand before the power operator combines the pair;
  // the negation nests as the left operand rather than wrapping the whole
  // exponentiation.
  auto* rhs = ParsePrecedenceRhs("module m; initial x = -a ** b; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPower);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kMinus);
}

TEST(Precedence, PowerHigherThanMultiply) {
  // Exponentiation is one tier above the multiplicative operators, so the power
  // folds into the right operand of the multiply.
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a * b ** c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kStar);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->op, TokenKind::kPower);
}

TEST(Precedence, AdditiveHigherThanShift) {
  // The additive operators bind tighter than the shift operators, so the sum
  // nests as the shift's left operand.
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a + b << c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kLtLt);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kPlus);
}

TEST(Precedence, BitwiseAndHigherThanXor) {
  // Bitwise AND sits above bitwise XOR, so the AND folds into the left operand
  // of the XOR.
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a & b ^ c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kCaret);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kAmp);
}

TEST(Precedence, XorHigherThanOr) {
  // Bitwise XOR sits above bitwise OR, so the XOR folds into the left operand
  // of the OR.
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a ^ b | c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kPipe);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kCaret);
}

TEST(Precedence, BitwiseOrHigherThanLogicalAnd) {
  // Bitwise OR binds tighter than the logical AND, so the OR nests as the
  // logical AND's left operand.
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a | b && c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kAmpAmp);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kPipe);
}

TEST(Precedence, LogicalAndHigherThanLogicalOr) {
  // Logical AND sits one tier above logical OR, so the AND folds into the left
  // operand of the OR.
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a && b || c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kPipePipe);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kAmpAmp);
}

TEST(Precedence, ConditionalHigherThanImplication) {
  // The conditional operator binds tighter than the implication operator, so
  // the conditional nests as the implication's right operand.
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
  // Shift operators share one row and associate left to right, so the leading
  // pair folds first.
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a << b >> c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kGtGt);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kLtLt);
}

TEST(Precedence, EqualityLeftAssoc) {
  // Equality operators share one row and associate left to right.
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a == b != c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kBangEq);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kEqEq);
}

TEST(Precedence, BitwiseAndLeftAssoc) {
  // Binary bitwise AND associates left to right.
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a & b & c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kAmp);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kAmp);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kIdentifier);
}

TEST(Precedence, BitwiseXorLeftAssoc) {
  // Binary bitwise XOR associates left to right.
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a ^ b ^ c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kCaret);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kCaret);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kIdentifier);
}

TEST(Precedence, BitwiseOrLeftAssoc) {
  // Binary bitwise OR associates left to right.
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a | b | c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kPipe);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kPipe);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kIdentifier);
}

TEST(Precedence, LogicalAndLeftAssoc) {
  // Logical AND associates left to right.
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a && b && c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kAmpAmp);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kAmpAmp);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kIdentifier);
}

TEST(Precedence, LogicalOrLeftAssoc) {
  // Logical OR associates left to right.
  auto* rhs =
      ParsePrecedenceRhs("module m; initial x = a || b || c; endmodule\n");
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kPipePipe);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kPipePipe);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kIdentifier);
}

}  // namespace
