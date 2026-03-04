#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserSection11, Sec11_4_1_BitSelectsInConcatenation) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial x = {data[7], data[6], data[5], data[4]};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kConcatenation);
  EXPECT_EQ(rhs->elements.size(), 4u);
  for (auto* elem : rhs->elements) {
    EXPECT_EQ(elem->kind, ExprKind::kSelect);
    EXPECT_EQ(elem->index_end, nullptr);
  }
}

TEST(ParserSection11, Sec11_4_1_IndexedPartSelectParamWidth) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  parameter W = 8;\n"
              "  logic [31:0] vec;\n"
              "  initial x = vec[0 +: W];\n"
              "endmodule\n"));
}

TEST(ParserSection11, Sec11_4_6_TernaryWithPartSelectOperands) {
  auto r = Parse(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial x = sel ? a[7:4] : b[7:4];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->true_expr, nullptr);
  EXPECT_EQ(rhs->true_expr->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->true_expr->index, nullptr);
  ASSERT_NE(rhs->true_expr->index_end, nullptr);
  ASSERT_NE(rhs->false_expr, nullptr);
  EXPECT_EQ(rhs->false_expr->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->false_expr->index_end, nullptr);
}
TEST(ParserSection11, IndexedPartSelectVariableBase) {
  auto r = Parse(
      "module t;\n"
      "  logic [63:0] dword;\n"
      "  integer sel;\n"
      "  initial x = dword[8*sel +: 8];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_plus);
}

TEST(ParserSection11, Sec11_1_BitSelectIndex) {
  auto r = Parse(
      "module t;\n"
      "  initial x = data[7];\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->base, nullptr);
  EXPECT_EQ(rhs->base->kind, ExprKind::kIdentifier);
  ASSERT_NE(rhs->index, nullptr);
  EXPECT_EQ(rhs->index->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->index_end, nullptr);
}

TEST(ParserSection11, Sec11_1_PartSelectIndexAndEnd) {
  auto r = Parse(
      "module t;\n"
      "  initial x = data[15:0];\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  ASSERT_NE(rhs->index, nullptr);
  ASSERT_NE(rhs->index_end, nullptr);
  EXPECT_FALSE(rhs->is_part_select_plus);
  EXPECT_FALSE(rhs->is_part_select_minus);
}

TEST(ParserSection11, Sec11_1_IndexedPartSelectPlusFlag) {
  auto r = Parse(
      "module t;\n"
      "  initial x = vec[i +: 4];\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_plus);
  EXPECT_FALSE(rhs->is_part_select_minus);
  ASSERT_NE(rhs->index, nullptr);
  ASSERT_NE(rhs->index_end, nullptr);
}

TEST(ParserSection11, Sec11_1_IndexedPartSelectMinusFlag) {
  auto r = Parse(
      "module t;\n"
      "  initial x = vec[j -: 8];\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(rhs->is_part_select_minus);
  EXPECT_FALSE(rhs->is_part_select_plus);
}

TEST(ParserSection11, BitSelect) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a[3];\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
}

TEST(ParserSection11, PartSelectConstant) {
  auto r = Parse(
      "module t;\n"
      "  initial x = a[7:0];\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSelect);
}

TEST(ParserSection7, Sec7_2_1_PackedIndexedPartSelectMinus) {
  auto r = Parse(
      "module t;\n"
      "  struct packed {\n"
      "    bit [7:0] a;\n"
      "    bit [7:0] b;\n"
      "    bit [7:0] c;\n"
      "    bit [7:0] d;\n"
      "  } s;\n"
      "  initial x = s[23 -: 8];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kSelect);
  EXPECT_TRUE(stmt->rhs->is_part_select_minus);
}

}
