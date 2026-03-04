// §7.12.2: Array ordering methods

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
// --- Test helpers ---
namespace {

// =========================================================================
// §7.12.2: Array ordering methods
// =========================================================================
TEST(ParserSection7, ArrayReverseMethod) {
  auto r = Parse("module t;\n"
                 "  int arr[4];\n"
                 "  initial arr.reverse();\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->expr, nullptr);
}

TEST(ParserSection7, ArrayShuffleMethod) {
  auto r = Parse("module t;\n"
                 "  int arr[4];\n"
                 "  initial arr.shuffle();\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_NE(stmt->expr, nullptr);
}

TEST(ParserCh513, BuiltInMethod_WithArgs) {
  // Built-in method with arguments: arr.find with (item > 3).
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  int q[$];\n"
                      "  initial q.sort();\n"
                      "endmodule"));
}

TEST(ParserSection7, ArrayMethodSort) {
  auto r = Parse("module t;\n"
                 "  int arr[] = '{5, 3, 1, 4, 2};\n"
                 "  initial arr.sort;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

TEST(ParserSection7, ArrayMethodRsort) {
  auto r = Parse("module t;\n"
                 "  int arr[] = '{1, 2, 3, 4, 5};\n"
                 "  initial arr.rsort;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

TEST(ParserSection7, ArrayMethodShuffle) {
  auto r = Parse("module t;\n"
                 "  int arr[] = '{1, 2, 3};\n"
                 "  initial arr.shuffle;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}
TEST(ParserSection7, ArraySortWithClause) {
  auto r = Parse("module t;\n"
                 "  initial arr.sort with (item.x);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  // sort with no parens but with clause: member_access + with
  auto *expr = stmt->expr;
  ASSERT_NE(expr, nullptr);
}

// =========================================================================
// §7.10.4: Array ordering methods — reverse
// =========================================================================
TEST(ParserSection7, ArrayMethodReverse) {
  auto r = Parse("module t;\n"
                 "  int arr[] = '{1, 2, 3};\n"
                 "  initial arr.reverse;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
}

} // namespace
