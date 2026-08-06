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

// §7.12: the with clause carries an expression enclosed in parentheses (as
// opposed to randomize's brace-delimited constraint set). The parser records
// the parenthesized form so later stages can tell the two apart.
TEST(ArrayMethodCallParsing, WithClauseUsesParentheses) {
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
  EXPECT_TRUE(rhs->with_has_parens);
}

// §7.12: when no with clause is present, a property or range select instead
// follows the array method call itself. This is the complement of
// PropertyAccessAfterWithClause and exercises the no-with branch.
TEST(ArrayMethodCallParsing, PropertyAccessWithoutWithClause) {
  auto r = Parse(
      "module t;\n"
      "  int arr[8];\n"
      "  int n;\n"
      "  initial n = arr.unique().size();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
