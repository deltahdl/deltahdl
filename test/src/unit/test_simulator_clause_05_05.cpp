#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

TEST(SimCh505, OperatorSingleCharInExpr) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd10 + 8'd20;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 30u);
}

TEST(SimCh505, OperatorDoubleCharInExpr) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd1 << 3;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 8u);
}

TEST(SimCh505, OperatorTripleCharInExpr) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd3 <<< 2;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 12u);
}

TEST(SimCh505, OperatorUnaryLeftOfOperand) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = -8'sd5;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result & 0xFF, 251u);
}

TEST(SimCh505, OperatorBinaryBetweenOperands) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd50 - 8'd15;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 35u);
}

TEST(SimCh505, OperatorConditionalThreeOperands) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 1 ? 8'd42 : 8'd99;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 42u);
}

TEST(SimCh505, OperatorConditionalFalseBranch) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 0 ? 8'd42 : 8'd99;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 99u);
}

TEST(SimCh505, OperatorMixedInExpression) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = (8'd3 + 8'd5) << 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 16u);
}

TEST(SimCh505, OperatorUnaryNegation) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = !1'b0;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 1u);
}

TEST(SimCh505, OperatorNoWhitespace) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result=8'd7+8'd3;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 10u);
}
