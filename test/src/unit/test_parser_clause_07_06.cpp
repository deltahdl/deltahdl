#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ArrayAssignmentParsing, ArrayAssignWhole) {
  auto r = Parse(
      "module t;\n"
      "  int a[4], b[4];\n"
      "  initial a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ArrayAssignmentParsing, ArraySliceAssign) {
  auto r = Parse(
      "module t;\n"
      "  int a[8], b[8];\n"
      "  initial a[3:0] = b[7:4];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

TEST(ArrayAssignmentParsing, ContinuousArrayAssign) {
  auto r = Parse(
      "module t;\n"
      "  int a[4], b[4];\n"
      "  assign a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ArrayAssignmentParsing, DynamicArrayAssign) {
  auto r = Parse(
      "module t;\n"
      "  int a[], b[];\n"
      "  initial a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
