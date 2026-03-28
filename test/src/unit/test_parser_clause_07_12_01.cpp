#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(AggregateTypeParsing, ArrayLocatorUnique) {
  auto r = Parse(
      "module t;\n"
      "  int s[] = '{10, 10, 3, 20, 20, 10};\n"
      "  int qi[$];\n"
      "  initial qi = s.unique;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kMemberAccess);
}

TEST(AggregateTypeParsing, ArrayLocatorFindWithClause) {
  auto r = Parse(
      "module t;\n"
      "  int arr[] = '{1, 2, 3, 4, 5};\n"
      "  int found[$];\n"
      "  initial found = arr.find with (item > 3);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(AggregateTypeParsing, ArrayLocatorFindIndex) {
  auto r = Parse(
      "module t;\n"
      "  int arr[] = '{10, 20, 30};\n"
      "  int idx[$];\n"
      "  initial idx = arr.find_index with (item == 20);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
}
TEST(AggregateTypeParsing, ArrayMethodMin) {
  auto r = Parse(
      "module t;\n"
      "  initial y = arr.min;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);

  EXPECT_EQ(rhs->kind, ExprKind::kMemberAccess);
}

TEST(SubroutineCallSyntaxParsing, ArrayMethodUnique) {
  auto r = Parse(
      "module m;\n"
      "  initial begin arr.unique(); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* expr = FirstInitialExpr(r);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kCall);
}

TEST(SubroutineCallSyntaxParsing, ArrayMethodWithClause) {
  auto r = Parse(
      "module m;\n"
      "  int arr[4];\n"
      "  int result[$];\n"
      "  initial begin result = arr.find with (item > 5); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AggregateTypeParsing, ArrayMethodMax) {
  auto r = Parse(
      "module t;\n"
      "  int arr[] = '{5, 1, 3};\n"
      "  int res[$];\n"
      "  initial res = arr.max;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kMemberAccess);
}

TEST(AggregateTypeParsing, ArrayMethodUniqueIndex) {
  auto r = Parse(
      "module t;\n"
      "  int arr[] = '{1, 2, 1, 3};\n"
      "  int idx[$];\n"
      "  initial idx = arr.unique_index;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kMemberAccess);
}

TEST(AggregateTypeParsing, ArrayLocatorFindFirst) {
  auto r = Parse(
      "module t;\n"
      "  int arr[] = '{1, 2, 3};\n"
      "  int found[$];\n"
      "  initial found = arr.find_first with (item > 1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(AggregateTypeParsing, ArrayLocatorFindLast) {
  auto r = Parse(
      "module t;\n"
      "  int arr[] = '{1, 2, 3};\n"
      "  int found[$];\n"
      "  initial found = arr.find_last with (item > 1);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(AggregateTypeParsing, ArrayLocatorFindFirstIndex) {
  auto r = Parse(
      "module t;\n"
      "  int arr[] = '{10, 20, 30};\n"
      "  int idx[$];\n"
      "  initial idx = arr.find_first_index with (item == 20);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(AggregateTypeParsing, ArrayLocatorFindLastIndex) {
  auto r = Parse(
      "module t;\n"
      "  int arr[] = '{10, 20, 30};\n"
      "  int idx[$];\n"
      "  initial idx = arr.find_last_index with (item > 10);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(AggregateTypeParsing, ArrayLocatorMinWithClause) {
  auto r = Parse(
      "module t;\n"
      "  int arr[] = '{5, 1, 3};\n"
      "  int res[$];\n"
      "  initial res = arr.min with (item);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_NE(stmt->rhs->with_expr, nullptr);
}

TEST(AggregateTypeParsing, ArrayLocatorMaxWithClause) {
  auto r = Parse(
      "module t;\n"
      "  int arr[] = '{5, 1, 3};\n"
      "  int res[$];\n"
      "  initial res = arr.max with (item);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_NE(stmt->rhs->with_expr, nullptr);
}

TEST(AggregateTypeParsing, ArrayLocatorUniqueWithClause) {
  auto r = Parse(
      "module t;\n"
      "  int arr[] = '{1, 2, 3};\n"
      "  int res[$];\n"
      "  initial res = arr.unique with (item % 2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_NE(stmt->rhs->with_expr, nullptr);
}

TEST(AggregateTypeParsing, ArrayLocatorUniqueIndexWithClause) {
  auto r = Parse(
      "module t;\n"
      "  int arr[] = '{1, 2, 3, 4};\n"
      "  int idx[$];\n"
      "  initial idx = arr.unique_index with (item % 2);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_NE(stmt->rhs->with_expr, nullptr);
}

}  // namespace
