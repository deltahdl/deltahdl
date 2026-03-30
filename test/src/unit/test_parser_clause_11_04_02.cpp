#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ExpressionParsing, PrefixIncrement) {
  auto r = Parse("module m; initial ++x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kUnary);
  EXPECT_EQ(expr->op, TokenKind::kPlusPlus);
}

TEST(ExpressionParsing, PrefixDecrement) {
  auto r = Parse("module m; initial --x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kUnary);
  EXPECT_EQ(expr->op, TokenKind::kMinusMinus);
}

TEST(ExpressionParsing, PostfixIncrement) {
  auto r = Parse("module m; initial x++; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kPostfixUnary);
  EXPECT_EQ(expr->op, TokenKind::kPlusPlus);
}

TEST(ExpressionParsing, PostfixDecrement) {
  auto r = Parse("module m; initial x--; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kPostfixUnary);
  EXPECT_EQ(expr->op, TokenKind::kMinusMinus);
}

TEST(ExpressionParsing, PrefixIncrementOnSelect) {
  auto r = Parse("module m; initial ++arr[0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kUnary);
  EXPECT_EQ(expr->lhs->kind, ExprKind::kSelect);
}

TEST(ExpressionParsing, PostfixDecrementOnMember) {
  auto r = Parse("module m; initial s.field--; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kPostfixUnary);
  EXPECT_EQ(expr->op, TokenKind::kMinusMinus);
}
TEST(OperatorAndExpressionParsing, PrefixDecrementInForStep) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    for (int i = 10; i > 0; --i)\n"
      "      x = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, PrefixIncAsSubexpression) {
  auto r = Parse("module m; initial x = ++y; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kPlusPlus);
}

TEST(ExpressionParsing, PostfixIncAsSubexpression) {
  auto r = Parse("module m; initial x = y++; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kPostfixUnary);
  EXPECT_EQ(rhs->op, TokenKind::kPlusPlus);
}

TEST(ExpressionParsing, NoParen_PrefixIncInBinaryExpr) {
  auto r = Parse("module m; initial x = ++y + 1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kPlusPlus);
}

TEST(ExpressionParsing, NoParen_PostfixDecInBinaryExpr) {
  auto r = Parse("module m; initial x = y-- + 1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kPostfixUnary);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kMinusMinus);
}

TEST(LvalueParsing, VarLvaluePreIncrement) {
  auto r = Parse("module m; int x; initial ++x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(LvalueParsing, VarLvaluePostIncrement) {
  auto r = Parse("module m; int x; initial x++; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(LvalueParsing, VarLvaluePreDecrement) {
  auto r = Parse("module m; int x; initial --x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(LvalueParsing, VarLvaluePostDecrement) {
  auto r = Parse("module m; int x; initial x--; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
