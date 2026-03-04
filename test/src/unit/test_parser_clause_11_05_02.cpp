#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection7, ArrayElementSelect) {
  auto r = Parse(
      "module t;\n"
      "  int arr[8];\n"
      "  initial x = arr[3];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSelect);
}

TEST(ParserSection7, MultiDimSelect) {
  auto r = Parse(
      "module t;\n"
      "  int arr[4][8];\n"
      "  initial x = arr[2][5];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSelect);
}

TEST(ParserSection11, Sec11_4_1_NestedBitSelects) {
  auto r = Parse(
      "module t;\n"
      "  logic [3:0] [7:0] packed_arr;\n"
      "  initial x = packed_arr[2][3];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_EQ(rhs->index_end, nullptr);
  ASSERT_NE(rhs->base, nullptr);
  EXPECT_EQ(rhs->base->kind, ExprKind::kSelect);
  EXPECT_EQ(rhs->base->index_end, nullptr);
}
TEST(ParserSection11, BitSelectChained) {
  auto r = Parse(
      "module t;\n"
      "  initial x = mem[i][j];\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->base, nullptr);
  EXPECT_EQ(rhs->base->kind, ExprKind::kSelect);
}

TEST(ParserA85, VarLvalueMultiDimSelect) {
  auto r = Parse(
      "module m; logic [7:0] mem [0:3][0:3];\n"
      "  initial mem[1][2] = 8'hAB;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

TEST(ParserSection11, ArrayThenPartSelect) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] twod[0:255][0:255];\n"
      "  initial x = twod[14][1][3:0];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}
