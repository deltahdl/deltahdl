#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(Precedence, NestedParenthesizedExpression) {
  auto r = Parse(
      "module t;\n"
      "  initial x = ((a + b) * (c - d));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kStar);
}

TEST(Precedence, ChainedAdditiveLeftAssoc) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a + b - c + d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
}
TEST(Precedence, ImplicationRightAssocParses) {
  auto r = Parse(
      "module t;\n"
      "  logic a, b, c, d;\n"
      "  initial d = a -> b -> c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kArrow);
}

TEST(Precedence, MultiplyHigherThanAdd) {
  auto r = Parse("module m; initial x = a + b * c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);

  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->rhs->op, TokenKind::kStar);
}

TEST(Precedence, ChainedBinaryOps) {
  auto r = Parse("module m; initial x = a | b & c ^ d; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
}

TEST(Precedence, ParenthesizedExpr) {
  auto r = Parse("module m; initial x = (a + b) * c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kStar);

  EXPECT_EQ(rhs->lhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->lhs->op, TokenKind::kPlus);
}

TEST(Precedence, ParenthesesOverrideBitwise) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a | b) & c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kAmp);
}

TEST(Precedence, ImplicationRightAssocStructure) {
  auto r = Parse(
      "module t;\n"
      "  logic a, b, c, d;\n"
      "  initial d = a -> b -> c;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);

  EXPECT_EQ(rhs->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->rhs->op, TokenKind::kArrow);
}

TEST(Precedence, NestedTernaryRightAssoc) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a ? b : c ? d : e;\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kTernary);
}

TEST(Precedence, ChainedTernaryRightAssoc) {
  auto r = Parse(
      "module t;\n"
      "  initial x = sel1 ? a : sel2 ? b : c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kIdentifier);

  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->false_expr->true_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->true_expr->kind, ExprKind::kIdentifier);
  ASSERT_NE(rhs->false_expr->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->false_expr->kind, ExprKind::kIdentifier);
}

TEST(Precedence, CompareAndLogicalWithParentheses) {
  auto r = Parse(
      "module t;\n"
      "  initial x = (a > 0) && (b < 10);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kAmpAmp);
}

}  // namespace
