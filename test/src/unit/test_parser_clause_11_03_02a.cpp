#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_precedence_rhs.h"

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

// Bitwise OR binds tighter than the logical AND on the right-hand side
// too, so the OR nests as the logical AND's right operand. The sibling
// file carries the left-operand case.
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

}  // namespace
