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

TEST(Precedence, PowerRightAssoc) {
  auto r = Parse(
      "module t;\n"
      "  initial x = 2 ** 3 ** 2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kPower);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->op, TokenKind::kPower);
}

TEST(Precedence, EqualityLowerThanRelational) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a < b == c < d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kEqEq);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kLt);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->op, TokenKind::kLt);
}

}  // namespace
