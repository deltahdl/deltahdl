#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(OperatorAndExpressionParsing, BitSelectsInConcatenation) {
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

TEST(OperatorAndExpressionParsing, IndexedPartSelectParamWidth) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  parameter W = 8;\n"
              "  logic [31:0] vec;\n"
              "  initial x = vec[0 +: W];\n"
              "endmodule\n"));
}

TEST(OperatorAndExpressionParsing, TernaryWithPartSelectOperands) {
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
TEST(OperatorAndExpressionParsing, IndexedPartSelectVariableBase) {
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

TEST(AggregateTypeParsing, PackedIndexedPartSelectMinus) {
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

}  // namespace
