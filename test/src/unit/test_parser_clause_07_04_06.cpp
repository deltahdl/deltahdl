#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ArrayOperationParsing, ArrayAssignWhole) {
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

TEST(ArrayOperationParsing, ArraySliceAssign) {
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

TEST(ArrayOperationParsing, ArrayEqualityExpression) {
  auto r = Parse(
      "module t;\n"
      "  int a[4], b[4];\n"
      "  logic eq;\n"
      "  initial eq = (a == b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kBinary);
}

TEST(ArrayOperationParsing, ArrayInequalityExpression) {
  auto r = Parse(
      "module t;\n"
      "  int a[4], b[4];\n"
      "  logic neq;\n"
      "  initial neq = (a != b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kBinary);
}

}  // namespace
