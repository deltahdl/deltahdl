#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

TEST(OperatorTokenSim, OperatorSingleCharInExpr) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd10 + 8'd20;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 30u);
}

TEST(OperatorTokenSim, OperatorDoubleCharInExpr) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd1 << 3;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 8u);
}

TEST(OperatorTokenSim, OperatorTripleCharInExpr) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd3 <<< 2;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 12u);
}

TEST(OperatorTokenSim, OperatorUnaryLeftOfOperand) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = -8'sd5;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result & 0xFF, 251u);
}

TEST(OperatorTokenSim, OperatorBinaryBetweenOperands) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd50 - 8'd15;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 35u);
}

TEST(OperatorTokenSim, OperatorConditionalThreeOperands) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 1 ? 8'd42 : 8'd99;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 42u);
}

TEST(OperatorTokenSim, OperatorConditionalFalseBranch) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 0 ? 8'd42 : 8'd99;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 99u);
}

TEST(OperatorTokenSim, OperatorMixedInExpression) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = (8'd3 + 8'd5) << 1;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 16u);
}

TEST(OperatorTokenSim, OperatorUnaryNegation) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = !1'b0;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 1u);
}

TEST(OperatorTokenSim, OperatorNoWhitespace) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result=8'd7+8'd3;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 10u);
}

TEST(OperatorTokenSim, OperatorBitwiseUnary) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = ~8'd0;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 255u);
}

TEST(OperatorTokenSim, OperatorChainedBinary) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd10 + 8'd20 - 8'd5;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 25u);
}

TEST(OperatorTokenSim, OperatorCompoundAssignment) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    result = 8'd10;\n"
      "    result += 8'd5;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 15u);
}
