#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

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
