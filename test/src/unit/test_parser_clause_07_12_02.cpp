#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(AggregateTypeParsing, ArrayReverseMethod) {
  auto r = Parse(
      "module t;\n"
      "  int arr[4];\n"
      "  initial arr.reverse();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->expr, nullptr);
}

TEST(AggregateTypeParsing, ArrayShuffleMethod) {
  auto r = Parse(
      "module t;\n"
      "  int arr[4];\n"
      "  initial arr.shuffle();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->expr, nullptr);
}

TEST(AggregateTypeParsing, ArrayMethodSort) {
  auto r = Parse(
      "module t;\n"
      "  int arr[] = '{5, 3, 1, 4, 2};\n"
      "  initial arr.sort;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

TEST(AggregateTypeParsing, ArrayMethodRsort) {
  auto r = Parse(
      "module t;\n"
      "  int arr[] = '{1, 2, 3, 4, 5};\n"
      "  initial arr.rsort;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

TEST(AggregateTypeParsing, ArrayMethodShuffle) {
  auto r = Parse(
      "module t;\n"
      "  int arr[] = '{1, 2, 3};\n"
      "  initial arr.shuffle;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}
TEST(AggregateTypeParsing, ArraySortWithClause) {
  auto r = Parse(
      "module t;\n"
      "  initial arr.sort with (item.x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);

  auto* expr = stmt->expr;
  ASSERT_NE(expr, nullptr);
  EXPECT_NE(expr->with_expr, nullptr);
}

TEST(AggregateTypeParsing, ArrayRsortWithClause) {
  auto r = Parse(
      "module t;\n"
      "  initial arr.rsort with (item.y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);

  auto* expr = stmt->expr;
  ASSERT_NE(expr, nullptr);
  EXPECT_NE(expr->with_expr, nullptr);
}

TEST(AggregateTypeParsing, ArraySortMethodCallWithParens) {
  auto r = Parse(
      "module t;\n"
      "  int arr[4];\n"
      "  initial arr.sort();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->expr, nullptr);
}

TEST(AggregateTypeParsing, ArrayRsortMethodCallWithParens) {
  auto r = Parse(
      "module t;\n"
      "  int arr[4];\n"
      "  initial arr.rsort();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->expr, nullptr);
}

TEST(AggregateTypeParsing, ArraySortWithIteratorAndWithClause) {
  auto r = Parse(
      "module t;\n"
      "  initial arr.sort(x) with ({x.blue, x.green});\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);

  auto* expr = stmt->expr;
  ASSERT_NE(expr, nullptr);
  EXPECT_NE(expr->with_expr, nullptr);
}

TEST(AggregateTypeParsing, ArrayMethodReverse) {
  auto r = Parse(
      "module t;\n"
      "  int arr[] = '{1, 2, 3};\n"
      "  initial arr.reverse;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

}  // namespace
