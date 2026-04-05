#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(DelayParsing, AssignDelayMinTypMaxNode) {
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

TEST(MinTypMaxParsing, FieldsAreMinTypMax) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a;\n"
      "  assign #(10:20:30) y = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* delay = r.cu->modules[0]->items[2]->assign_delay;
  ASSERT_NE(delay, nullptr);
  ASSERT_EQ(delay->kind, ExprKind::kMinTypMax);
  ASSERT_NE(delay->lhs, nullptr);
  ASSERT_NE(delay->condition, nullptr);
  ASSERT_NE(delay->rhs, nullptr);
  EXPECT_EQ(delay->lhs->int_val, 10u);
  EXPECT_EQ(delay->condition->int_val, 20u);
  EXPECT_EQ(delay->rhs->int_val, 30u);
}

TEST(MinTypMaxParsing, SubExpressions) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire y, a;\n"
              "  assign #(1+2 : 3+4 : 5+6) y = a;\n"
              "endmodule\n"));
}

TEST(MinTypMaxParsing, MultipleGateDelays) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire a, b, c;\n"
              "  and #(1:2:3, 4:5:6) g1(c, a, b);\n"
              "endmodule\n"));
}

TEST(MinTypMaxParsing, ProceduralDelayStatement) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    #(1:2:3);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
