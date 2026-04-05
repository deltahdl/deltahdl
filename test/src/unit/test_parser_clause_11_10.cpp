#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(OperatorAndExpressionParsing, StringLiteralAsExpression) {
  auto r = Parse(
      "module t;\n"
      "  string s;\n"
      "  initial s = \"hello world\";\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStringLiteral);
}

TEST(OperatorAndExpressionParsing, StringLiteralWideVector) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  bit [8*20:1] wide;\n"
              "  initial wide = \"short\";\n"
              "endmodule\n"));
}

TEST(OperatorAndExpressionParsing, MultiCharStringLiteralInExpression) {
  auto r = Parse(
      "module t;\n"
      "  bit [8*2:1] s;\n"
      "  initial s = \"AB\";\n"
      "endmodule\n");
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStringLiteral);
}

TEST(OperatorAndExpressionParsing, StringLiteralWithArithmeticOperator) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  bit [7:0] r;\n"
              "  initial r = \"A\" + 8'd1;\n"
              "endmodule\n"));
}

TEST(OperatorAndExpressionParsing, StringLiteralWithBitwiseOperator) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  bit [7:0] r;\n"
              "  initial r = \"A\" | 8'h20;\n"
              "endmodule\n"));
}

TEST(OperatorAndExpressionParsing, StringLiteralWithRelationalOperator) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic r;\n"
              "  initial r = \"B\" > \"A\";\n"
              "endmodule\n"));
}

}  // namespace
