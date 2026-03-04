#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection7, ArraySumMethod) {
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

TEST(ParserSection7, ArraySumWithClause) {
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

TEST(ParserSection7, ArrayProductMethod) {
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

TEST(ParserSection7, ArrayReductionAnd) {
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

TEST(ParserSection7, ArrayReductionOr) {
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

TEST(ParserSection7, ArrayReductionXor) {
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

TEST(ParserSection7, ArrayReductionSum) {
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

TEST(ParserA609, ArrayMethodAnd) {
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

TEST(ParserA609, ArrayMethodOr) {
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

TEST(ParserA609, ArrayMethodXor) {
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

TEST(ParserA82, ArrayManipCallSum) {
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

TEST(ParserA82, ArrayMethodNameAnd) {
  auto r = Parse(
      "module m;\n"
      "  initial begin x = arr.and(); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA82, ArrayMethodNameOr) {
  auto r = Parse(
      "module m;\n"
      "  initial begin x = arr.or(); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA82, ArrayMethodNameXor) {
  auto r = Parse(
      "module m;\n"
      "  initial begin x = arr.xor(); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}
