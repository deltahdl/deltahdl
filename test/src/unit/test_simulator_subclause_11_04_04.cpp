#include <gtest/gtest.h>

#include <string>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "lexer/token.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(RelationalEval, KnownOperandsYieldDefiniteResult) {
  SimFixture f;

  auto* expr = MakeBinary(f.arena, TokenKind::kLt, MakeInt(f.arena, 3),
                          MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(RelationalEval, FalseResultIsSingleBit) {
  SimFixture f;
  auto* expr = MakeBinary(f.arena, TokenKind::kGt, MakeInt(f.arena, 3),
                          MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
  EXPECT_EQ(result.ToUint64(), 0u);
  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(OperatorSim, BinaryLessThan) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd3 < 8'd5);\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, BinaryGreaterThan) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd10 > 8'd3);\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, BinaryGreaterOrEqual) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd5 >= 8'd5);\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, BinaryLessOrEqual) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd5 <= 8'd5);\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, FalseRelationalResult) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd3 > 8'd5);\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(OperatorSim, RelationalXOperandYieldsX) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b1x00;\n"
      "    b = 4'b0100;\n"
      "    r = (a < b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 1u);
  EXPECT_NE(var->value.words[0].bval & 1u, 0u);
}

TEST(OperatorSim, RelationalZOperandYieldsX) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'b1000;\n"
      "    b = 4'b0z10;\n"
      "    r = (a > b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 1u);
  EXPECT_NE(var->value.words[0].bval & 1u, 0u);
}

TEST(OperatorSim, UnsignedUnequalWidthZeroExtends) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a;\n"
      "  logic [7:0] b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 4'hF;\n"
      "    b = 8'h10;\n"
      "    r = (a < b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, UnsignedHighValueNotLessThan) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 8'hFF;\n"
      "    b = 8'h01;\n"
      "    r = (a < b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(OperatorSim, MixedSignedUnsignedUsesUnsigned) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic signed [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = -1;\n"
      "    b = 8'h01;\n"
      "    r = (a < b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 1u);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(OperatorSim, SignedUnequalWidthSignExtends) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic signed [3:0] a;\n"
      "  logic signed [7:0] b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = -2;\n"
      "    b = 8'sd5;\n"
      "    r = (a < b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, SignedNegativeLessThanPositive) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic signed [7:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = -1;\n"
      "    b = 1;\n"
      "    r = (a < b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, SignedPositiveGreaterThanNegative) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic signed [7:0] a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = -1;\n"
      "    r = (a > b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, RealOperandConvertsIntegerOperand) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  real ra;\n"
      "  int i;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    ra = 2.5;\n"
      "    i = 3;\n"
      "    r = (ra < i);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 1u);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, RealComparisonFalseResult) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  real a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = 1.0;\n"
      "    b = 2.0;\n"
      "    r = (a >= b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 1u);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(OperatorSim, RealOnRightConvertsLeftOperand) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int i;\n"
      "  real x;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    i = 3;\n"
      "    x = 2.5;\n"
      "    r = (i > x);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 1u);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, IntegerOperandsCompareSigned) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  integer a, b;\n"
      "  logic r;\n"
      "  initial begin\n"
      "    a = -1;\n"
      "    b = 1;\n"
      "    r = (a < b);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, SignedNetOperandsCompareSigned) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire signed [7:0] a, b;\n"
      "  wire r;\n"
      "  assign a = -1;\n"
      "  assign b = 1;\n"
      "  assign r = (a < b);\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(OperatorSim, UnsignedNetOperandsCompareUnsigned) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire [7:0] a, b;\n"
      "  wire r;\n"
      "  assign a = 8'hFF;\n"
      "  assign b = 8'h01;\n"
      "  assign r = (a < b);\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(RelationalOperatorSim, OperandsAreComparedOverEveryWord) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  logic [127:0] a = 128'h1 << 100, b = 128'h1;\n"
                 "  logic signed [127:0] n = -1, p = 1;\n"
                 "  initial $display(\"%b %b %b %b %b %b\", a > b, a <= b,\n"
                 "                   n < p, p < n, a >= a, b < a);\n"
                 "endmodule\n",
                 f),
      "1 0 1 0 1 1\n");
}

}  // namespace
