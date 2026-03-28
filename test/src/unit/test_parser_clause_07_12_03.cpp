#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(AggregateTypeParsing, ArraySumMethod) {
  auto r = Parse(
      "module t;\n"
      "  int arr[4];\n"
      "  initial x = arr.sum;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kMemberAccess);
}

TEST(AggregateTypeParsing, ArraySumWithClause) {
  auto r = Parse(
      "module t;\n"
      "  int arr[4];\n"
      "  initial x = arr.sum with (item * 2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(AggregateTypeParsing, ArrayProductMethod) {
  auto r = Parse(
      "module t;\n"
      "  int arr[4];\n"
      "  initial x = arr.product;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(AggregateTypeParsing, ArrayReductionAnd) {
  auto r = Parse(
      "module t;\n"
      "  byte b[] = '{1, 3, 5, 7};\n"
      "  initial y = b.and;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kMemberAccess);
}

TEST(AggregateTypeParsing, ArrayReductionOr) {
  auto r = Parse(
      "module t;\n"
      "  byte b[] = '{1, 2, 3, 4};\n"
      "  initial y = b.or;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kMemberAccess);
}

TEST(AggregateTypeParsing, ArrayReductionXor) {
  auto r = Parse(
      "module t;\n"
      "  byte b[] = '{1, 2, 3, 4};\n"
      "  initial y = b.xor;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kMemberAccess);
}

TEST(AggregateTypeParsing, ArrayReductionSum) {
  auto r = Parse(
      "module t;\n"
      "  int arr[] = '{1, 2, 3};\n"
      "  initial y = arr.sum;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kMemberAccess);
}

TEST(SubroutineCallSyntaxParsing, ArrayMethodAnd) {
  auto r = Parse(
      "module m;\n"
      "  initial begin arr.and(); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
}

TEST(SubroutineCallSyntaxParsing, ArrayMethodOr) {
  auto r = Parse(
      "module m;\n"
      "  initial begin arr.or(); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
}

TEST(SubroutineCallSyntaxParsing, ArrayMethodXor) {
  auto r = Parse(
      "module m;\n"
      "  initial begin arr.xor(); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
}

TEST(SubroutineCallExprParsing, SumCallExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial begin x = arr.sum(); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
}

TEST(SubroutineCallExprParsing, AndCallExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial begin x = arr.and(); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SubroutineCallExprParsing, OrCallExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial begin x = arr.or(); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SubroutineCallExprParsing, XorCallExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial begin x = arr.xor(); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- product() call syntax ---

TEST(SubroutineCallExprParsing, ProductCallExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial begin x = arr.product(); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kCall);
}

// --- with clause for each reduction method ---

TEST(AggregateTypeParsing, ProductWithClause) {
  auto r = Parse(
      "module t;\n"
      "  int arr[4];\n"
      "  initial x = arr.product with (item + 1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AggregateTypeParsing, AndWithClause) {
  auto r = Parse(
      "module t;\n"
      "  byte b[4];\n"
      "  initial y = b.and with (item);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AggregateTypeParsing, OrWithClause) {
  auto r = Parse(
      "module t;\n"
      "  byte b[4];\n"
      "  initial y = b.or with (item);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AggregateTypeParsing, XorWithClause) {
  auto r = Parse(
      "module t;\n"
      "  byte b[4];\n"
      "  initial y = b.xor with (item + 4);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- with clause populates with_expr on AST ---

TEST(AggregateTypeParsing, SumWithClausePopulatesWithExpr) {
  auto r = Parse(
      "module t;\n"
      "  int arr[4];\n"
      "  initial x = arr.sum with (item * 2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_NE(rhs->with_expr, nullptr);
}

// --- custom iterator argument ---

TEST(AggregateTypeParsing, ReductionWithCustomIterator) {
  auto r = Parse(
      "module t;\n"
      "  int arr[4];\n"
      "  initial x = arr.sum(x) with (x * 2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
