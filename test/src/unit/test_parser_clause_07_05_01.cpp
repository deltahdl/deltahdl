#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DynamicArrayNewParsing, DynamicArrayDeclWithNew) {
  auto r = Parse(
      "module m;\n"
      "  int d[] = new[5];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}
TEST(DynamicArrayNewParsing, BlockingAssignment_DynamicArrayNew) {
  auto r = Parse(
      "module m;\n"
      "  initial begin arr = new[10]; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(DynamicArrayNewParsing, BlockingAssignment_DynamicArrayNewWithInit) {
  auto r = Parse(
      "module m;\n"
      "  initial begin arr = new[10](old_arr); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(DynamicArrayNewParsing, DynamicArrayNew) {
  auto r = Parse(
      "module t;\n"
      "  int dyn[];\n"
      "  initial dyn = new[10];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(DynamicArrayNewParsing, DynamicArrayNewWithInit) {
  auto r = Parse(
      "module t;\n"
      "  int dyn[];\n"
      "  int src[];\n"
      "  initial dyn = new[20](src);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

}  // namespace
