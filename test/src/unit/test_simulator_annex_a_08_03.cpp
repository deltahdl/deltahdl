#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ExpressionSim, ConditionalExpressionSimulates) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [7:0] x;\n"
                      "  initial x = 1 ? 8'd42 : 8'd0;\n"
                      "endmodule\n",
                      "x"),
            42u);
}

TEST(ExpressionSim, ConditionalExpressionFalseBranch) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [7:0] x;\n"
                      "  initial x = 0 ? 8'd42 : 8'd99;\n"
                      "endmodule\n",
                      "x"),
            99u);
}

TEST(ExpressionSim, PostfixIncrementSimulates) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  integer i;\n"
                      "  initial begin\n"
                      "    i = 5;\n"
                      "    i++;\n"
                      "  end\n"
                      "endmodule\n",
                      "i"),
            6u);
}

TEST(ExpressionSim, PrefixDecrementSimulates) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  integer i;\n"
                      "  initial begin\n"
                      "    i = 5;\n"
                      "    --i;\n"
                      "  end\n"
                      "endmodule\n",
                      "i"),
            4u);
}

TEST(ExpressionSim, ConstantExpressionInParameterSimulates) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  parameter P = 3 + 4;\n"
                      "  logic [7:0] x;\n"
                      "  initial x = P;\n"
                      "endmodule\n",
                      "x"),
            7u);
}

TEST(ExpressionSim, ConstantTernaryInParameterSimulates) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  parameter A = 1;\n"
                      "  parameter B = A ? 8'd10 : 8'd20;\n"
                      "  logic [7:0] x;\n"
                      "  initial x = B;\n"
                      "endmodule\n",
                      "x"),
            10u);
}

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
  LowerRunAndCheck(f, design,
                   {
                       {"sum", 7u},
                       {"diff", 7u},
                       {"prod", 30u},
                       {"quot", 5u},
                       {"rem", 2u},
                   });
}

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
  LowerRunAndCheck(f, design,
                   {
                       {"a", 0x00u},
                       {"b", 0xFFu},
                   });
}

TEST(ExpressionSim, PartSelectRangeSimulates) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [15:0] data;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    data = 16'hABCD;\n"
                      "    x = data[15:8];\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            0xABu);
}

TEST(ExpressionSim, IndexedRangePlusSimulates) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [15:0] data;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    data = 16'hABCD;\n"
                      "    x = data[8+:8];\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            0xABu);
}

TEST(ExpressionSim, IndexedRangeMinusSimulates) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [15:0] data;\n"
                      "  logic [7:0] x;\n"
                      "  initial begin\n"
                      "    data = 16'hABCD;\n"
                      "    x = data[15-:8];\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            0xABu);
}

TEST(ExpressionSim, NestedTernarySimulates) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [7:0] x;\n"
                      "  initial x = 0 ? 8'd1 : 1 ? 8'd2 : 8'd3;\n"
                      "endmodule\n",
                      "x"),
            2u);
}

TEST(ExpressionSim, InsideExpressionHitSimulates) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [7:0] x;\n"
                      "  logic hit;\n"
                      "  initial begin\n"
                      "    x = 8'd5;\n"
                      "    hit = x inside {1, 2, [4:6], 9};\n"
                      "  end\n"
                      "endmodule\n",
                      "hit"),
            1u);
}

TEST(ExpressionSim, InsideExpressionMissSimulates) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [7:0] x;\n"
                      "  logic hit;\n"
                      "  initial begin\n"
                      "    x = 8'd99;\n"
                      "    hit = x inside {1, 2, [4:6], 9};\n"
                      "  end\n"
                      "endmodule\n",
                      "hit"),
            0u);
}

TEST(ExpressionSim, TaggedUnionExpressionSimulates) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int x;\n"
                      "  initial x = tagged Valid 42;\n"
                      "endmodule\n",
                      "x"),
            42u);
}

TEST(ExpressionSim, ExprOperatorAssignmentSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  integer x, y;\n"
      "  initial begin\n"
      "    y = 1;\n"
      "    x = (y += 2);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {
                       {"y", 3u},
                       {"x", 3u},
                   });
}

}  // namespace
