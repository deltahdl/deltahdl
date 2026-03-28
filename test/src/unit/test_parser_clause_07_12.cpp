#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ArrayMethodCallParsing, WithClausePopulatesWithExpr) {
  auto r = Parse(
      "module t;\n"
      "  int arr[4];\n"
      "  int result[$];\n"
      "  initial result = arr.find with (item > 3);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_NE(rhs->with_expr, nullptr);
}

TEST(ArrayMethodCallParsing, NoWithClauseLeavesWithExprNull) {
  auto r = Parse(
      "module t;\n"
      "  int arr[4];\n"
      "  initial arr.reverse();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->with_expr, nullptr);
}

TEST(ArrayMethodCallParsing, IteratorArgumentWithWithClause) {
  auto r = Parse(
      "module t;\n"
      "  int arr[4];\n"
      "  int result[$];\n"
      "  initial result = arr.find(x) with (x > 3);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_NE(rhs->with_expr, nullptr);
}

TEST(ArrayMethodCallParsing, IteratorAndIndexArguments) {
  auto r = Parse(
      "module t;\n"
      "  int arr[4];\n"
      "  int result[$];\n"
      "  initial result = arr.find(x, idx) with (x > 0);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_NE(rhs->with_expr, nullptr);
}

TEST(ArrayMethodCallParsing, PropertyAccessAfterWithClause) {
  auto r = Parse(
      "module t;\n"
      "  int arr[8];\n"
      "  int result[$];\n"
      "  initial result = arr.find(x) with (x > 5).unique;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
