#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §A.8.3: conditional_expression simulates
TEST(ExpressionSim, ConditionalExpressionSimulates) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 1 ? 8'd42 : 8'd0;\n"
      "endmodule\n",
      "x"), 42u);
}

// §A.8.3: conditional_expression — false branch
TEST(ExpressionSim, ConditionalExpressionFalseBranch) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 0 ? 8'd42 : 8'd99;\n"
      "endmodule\n",
      "x"), 99u);
}

// §A.8.3: inc_or_dec_expression — postfix increment
TEST(ExpressionSim, PostfixIncrementSimulates) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    i = 5;\n"
      "    i++;\n"
      "  end\n"
      "endmodule\n",
      "i"), 6u);
}

// §A.8.3: inc_or_dec_expression — prefix decrement
TEST(ExpressionSim, PrefixDecrementSimulates) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    i = 5;\n"
      "    --i;\n"
      "  end\n"
      "endmodule\n",
      "i"), 4u);
}

// §A.8.3: constant_expression in parameter used at simulation
TEST(ExpressionSim, ConstantExpressionInParameterSimulates) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  parameter P = 3 + 4;\n"
      "  logic [7:0] x;\n"
      "  initial x = P;\n"
      "endmodule\n",
      "x"), 7u);
}

// §A.8.3: constant_expression — ternary in parameter
TEST(ExpressionSim, ConstantTernaryInParameterSimulates) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  parameter A = 1;\n"
      "  parameter B = A ? 8'd10 : 8'd20;\n"
      "  logic [7:0] x;\n"
      "  initial x = B;\n"
      "endmodule\n",
      "x"), 10u);
}

// §A.8.3: expression — binary operators simulate correctly
TEST(ExpressionSim, BinaryOperatorsSimulate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sum, diff, prod, quot, rem;\n"
      "  initial begin\n"
      "    sum  = 8'd3 + 8'd4;\n"
      "    diff = 8'd10 - 8'd3;\n"
      "    prod = 8'd5 * 8'd6;\n"
      "    quot = 8'd20 / 8'd4;\n"
      "    rem  = 8'd17 % 8'd5;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {
      {"sum", 7u},
      {"diff", 7u},
      {"prod", 30u},
      {"quot", 5u},
      {"rem", 2u},
  });
}

// §A.8.3: expression — unary operators simulate correctly
TEST(ExpressionSim, UnaryOperatorsSimulate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = ~8'hFF;\n"
      "    b = -8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {
      {"a", 0x00u},
      {"b", 0xFFu},
  });
}

// §A.8.3: part_select_range simulates
TEST(ExpressionSim, PartSelectRangeSimulates) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  logic [15:0] data;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    data = 16'hABCD;\n"
      "    x = data[15:8];\n"
      "  end\n"
      "endmodule\n",
      "x"), 0xABu);
}

// §A.8.3: indexed_range — ascending part select simulates
TEST(ExpressionSim, IndexedRangePlusSimulates) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  logic [15:0] data;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    data = 16'hABCD;\n"
      "    x = data[8+:8];\n"
      "  end\n"
      "endmodule\n",
      "x"), 0xABu);
}

// §A.8.3: indexed_range — descending part select simulates
TEST(ExpressionSim, IndexedRangeMinusSimulates) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  logic [15:0] data;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    data = 16'hABCD;\n"
      "    x = data[15-:8];\n"
      "  end\n"
      "endmodule\n",
      "x"), 0xABu);
}

// §A.8.3: nested conditional expression simulates
TEST(ExpressionSim, NestedTernarySimulates) {
  EXPECT_EQ(RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 0 ? 8'd1 : 1 ? 8'd2 : 8'd3;\n"
      "endmodule\n",
      "x"), 2u);
}

}  // namespace
