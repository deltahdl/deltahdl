#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(Precedence, ShiftLowerThanAdd) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a + b << c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kLtLt);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kPlus);
}

TEST(Precedence, BitwiseAndHigherThanXor) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a & b ^ c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kCaret);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kAmp);
}

TEST(Precedence, XorHigherThanOr) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a ^ b | c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kPipe);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kCaret);
}

TEST(Precedence, LogicalAndHigherThanOr) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a && b || c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kPipePipe);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kAmpAmp);
}

TEST(Precedence, EquivalenceRightAssoc) {
  auto r = Parse(
      "module t;\n"
      "  logic a, b, c, d;\n"
      "  initial d = a <-> b <-> c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kLtDashGt);

  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->op, TokenKind::kLtDashGt);
}

TEST(Precedence, PowerLeftAssoc) {
  auto r = Parse(
      "module t;\n"
      "  initial x = 2 ** 3 ** 2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kPower);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kPower);
}

TEST(Precedence, ShiftHigherThanComparison) {
  auto r = Parse("module m; initial x = a < b << c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kLt);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->rhs->op, TokenKind::kLtLt);
}

TEST(Precedence, EqualityHigherThanBitwiseAnd) {
  auto r = Parse("module m; initial x = a & b == c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kAmp);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->rhs->op, TokenKind::kEqEq);
}

TEST(Precedence, BitwiseOrHigherThanLogicalAnd) {
  auto r = Parse("module m; initial x = a && b | c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kAmpAmp);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->rhs->op, TokenKind::kPipe);
}

TEST(Precedence, UnaryHigherThanBinary) {
  auto r = Parse("module m; initial x = ~a & b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kAmp);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kTilde);
}

TEST(Precedence, PowerHigherThanMultiply) {
  auto r = Parse("module m; initial x = a * b ** c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kStar);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->op, TokenKind::kPower);
}

TEST(Precedence, LogicalOrHigherThanTernary) {
  auto r = Parse("module m; initial x = a || b ? c : d; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->condition, nullptr);
  EXPECT_EQ(rhs->condition->op, TokenKind::kPipePipe);
}

TEST(Precedence, TernaryHigherThanImplication) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, c, d, e;\n"
      "  initial e = a -> b ? c : d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kArrow);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kTernary);
}

TEST(Precedence, WildcardEqualitySamePrecedenceAsLogicalEquality) {
  auto r = Parse("module m; initial x = a ==? b != c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kBangEq);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kEqEqQuestion);
}

TEST(Precedence, ArithShiftSamePrecedenceAsLogicShift) {
  auto r = Parse("module m; initial x = a <<< b >> c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kGtGt);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kLtLtLt);
}

TEST(Precedence, MultiplyLeftAssoc) {
  auto r = Parse("module m; initial x = a * b / c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kSlash);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kStar);
}

TEST(Precedence, ModulusSamePrecedenceAsMultiply) {
  auto r = Parse("module m; initial x = a % b * c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kStar);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kPercent);
}

TEST(Precedence, ShiftLeftAssoc) {
  auto r = Parse("module m; initial x = a << b >> c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kGtGt);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kLtLt);
}

TEST(Precedence, EqualityLeftAssoc) {
  auto r = Parse("module m; initial x = a == b != c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kBangEq);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kEqEq);
}

TEST(Precedence, BitwiseAndLeftAssoc) {
  auto r = Parse("module m; initial x = a & b & c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kAmp);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kAmp);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kIdentifier);
}

TEST(Precedence, BitwiseXorLeftAssoc) {
  auto r = Parse("module m; initial x = a ^ b ^ c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kCaret);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kCaret);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kIdentifier);
}

TEST(Precedence, BitwiseOrLeftAssoc) {
  auto r = Parse("module m; initial x = a | b | c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kPipe);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kPipe);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kIdentifier);
}

TEST(Precedence, LogicalAndLeftAssoc) {
  auto r = Parse("module m; initial x = a && b && c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kAmpAmp);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kAmpAmp);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kIdentifier);
}

TEST(Precedence, LogicalOrLeftAssoc) {
  auto r = Parse("module m; initial x = a || b || c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kPipePipe);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kPipePipe);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kIdentifier);
}

TEST(Precedence, AllPrecedenceLevelsInOneExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial x = a || b && c | d ^ e & f == g < h << i + j * k;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kPipePipe);
}

}  // namespace
