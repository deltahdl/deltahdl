#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA24, DynamicArrayNewSize) {
  auto r = Parse(
      "module m;\n"
      "  int d[];\n"
      "  initial d = new[10];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA24, DynamicArrayNewSizeAndInit) {
  auto r = Parse(
      "module m;\n"
      "  int d[];\n"
      "  int src [10];\n"
      "  initial d = new[10](src);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA24, DynamicArrayDeclWithNew) {
  auto r = Parse(
      "module m;\n"
      "  int d[] = new[5];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}
TEST(ParserA602, BlockingAssignment_DynamicArrayNew) {
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

TEST(ParserA602, BlockingAssignment_DynamicArrayNewWithInit) {
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

TEST(ParserSection7c, DynamicArrayNewConstruct) {
  auto r = Parse(
      "module m;\n"
      "  int dyn[];\n"
      "  initial dyn = new[10];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection7, DynamicArrayNew) {
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

TEST(ParserSection7, DynamicArrayNewWithInit) {
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

}
