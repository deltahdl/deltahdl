// §11.4.10: Shift operators

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// =========================================================================
// Section 11.4.10 -- Arithmetic shift operators
// =========================================================================
TEST(ParserSection11, ArithmeticShiftLeft) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a <<< 2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kLtLtLt);
}

TEST(ParserSection11, ArithmeticShiftRight) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a >>> 2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kGtGtGt);
}

// =============================================================================
// A.8.6 Operators — binary_operator (shift)
// =============================================================================
// § binary_operator ::= >>
TEST(ParserA86, BinaryLogicalRightShift) {
  auto r = Parse("module m; initial x = a >> 2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kGtGt);
}

// § binary_operator ::= <<
TEST(ParserA86, BinaryLogicalLeftShift) {
  auto r = Parse("module m; initial x = a << 2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kLtLt);
}

// § binary_operator ::= >>>
TEST(ParserA86, BinaryArithRightShift) {
  auto r = Parse("module m; initial x = a >>> 2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kGtGtGt);
}

// § binary_operator ::= <<<
TEST(ParserA86, BinaryArithLeftShift) {
  auto r = Parse("module m; initial x = a <<< 2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kLtLtLt);
}

// Shift operators
TEST(ParserA83, ExprLeftShift) {
  auto r = Parse("module m; initial x = a << 2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kLtLt);
}

TEST(ParserA83, ExprRightShift) {
  auto r = Parse("module m; initial x = a >> 2; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kGtGt);
}

// =========================================================================
// Section 11.4.10 -- Shift operators (logical)
// =========================================================================
TEST(ParserSection11, LogicalShiftLeft) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a << 2;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kLtLt);
}

TEST(ParserSection11, LogicalShiftRight) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a >> 2;\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kGtGt);
}

TEST(ParserCh505, Operator_LogicalShiftLeft) {
  EXPECT_TRUE(ParseOk("module m; initial x = a <<< 2; endmodule"));
}

TEST(ParserCh505, Operator_ArithShiftRight) {
  EXPECT_TRUE(ParseOk("module m; initial x = a >>> 1; endmodule"));
}

}  // namespace
