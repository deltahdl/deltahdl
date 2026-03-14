#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(DelayParsing, Delay2MintypMaxSingleValue) {
  auto r = Parse(
      "module m;\n"
      "  wire out, in;\n"
      "  assign #(1:2:3) out = in;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[2];
  ASSERT_NE(item->assign_delay, nullptr);
  EXPECT_EQ(item->assign_delay->kind, ExprKind::kMinTypMax);
}

TEST(ExpressionParsing, ConstantMinTypMaxInSpecparam) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam tpd = 1:2:3;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, MinTypMaxInDelay) {
  auto r = Parse(
      "module m;\n"
      "  wire y;\n"
      "  assign #(1:2:3) y = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ExpressionParsing, MinTypMaxSingleExpr) {
  auto r = Parse(
      "module m;\n"
      "  wire y;\n"
      "  assign #5 y = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PrimaryParsing, ConstantPrimaryParenthesized) {
  auto r = Parse("module m; parameter int P = (1 + 2); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* param = r.cu->modules[0]->items[0];
  ASSERT_NE(param->init_expr, nullptr);
  EXPECT_EQ(param->init_expr->kind, ExprKind::kBinary);
}

TEST(OperatorAndExpressionParsing, MinTypMaxInGateDelay) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  wire a, b, c;\n"
              "  and #(2:3:4) g1(c, a, b);\n"
              "endmodule\n"));
}

TEST(OperatorAndExpressionParsing, MinTypMaxInSpecparam) {
  EXPECT_TRUE(
      ParseOk("module t(input a, output b);\n"
              "  specify\n"
              "    specparam tRise = 1:2:3;\n"
              "  endspecify\n"
              "endmodule\n"));
}

}  // namespace
