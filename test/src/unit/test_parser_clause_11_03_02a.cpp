#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// §11.3.2: Shift operators have lower precedence than add/sub.
// a + b << c should parse as (a + b) << c.
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

// §11.3.2: Bitwise AND has higher precedence than bitwise XOR.
// a & b ^ c should parse as (a & b) ^ c.
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

// §11.3.2: Bitwise XOR has higher precedence than bitwise OR.
// a ^ b | c should parse as (a ^ b) | c.
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

// §11.3.2: Logical AND (&&) has higher precedence than logical OR (||).
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

// §11.3.2: Equivalence (<->) right-associates.
// a <-> b <-> c should parse as a <-> (b <-> c).
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
  // Right-assoc: rhs should also be <->
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->op, TokenKind::kLtDashGt);
}

// §11.3.2: Power (**) right-associates.
// 2 ** 3 ** 2 should parse as 2 ** (3 ** 2).
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

// §11.3.2: Equality operators have lower precedence than relational.
// a < b == c < d should parse as (a < b) == (c < d).
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
