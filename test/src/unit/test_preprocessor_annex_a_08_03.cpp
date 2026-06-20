#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ExpressionPreprocessor, ConditionalExpressionPassesThrough) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("module m;\n"
                              "  logic [7:0] a, b, c, x;\n"
                              "  initial x = a ? b : c;\n"
                              "endmodule\n"));
}

TEST(ExpressionPreprocessor, IncDecExpressionPassesThrough) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("module m;\n"
                              "  integer i;\n"
                              "  initial begin\n"
                              "    i = 0;\n"
                              "    ++i;\n"
                              "    i--;\n"
                              "  end\n"
                              "endmodule\n"));
}

TEST(ExpressionPreprocessor, InsideExpressionPassesThrough) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("module m;\n"
                              "  logic [7:0] x;\n"
                              "  logic hit;\n"
                              "  initial hit = x inside {1, 2, [4:6]};\n"
                              "endmodule\n"));
}

TEST(ExpressionPreprocessor, TaggedUnionExpressionPassesThrough) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("module m;\n"
                              "  int x;\n"
                              "  initial x = tagged Valid 42;\n"
                              "endmodule\n"));
}

TEST(ExpressionPreprocessor, MacroExpandsToConstantExpression) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`define W 8\n"
                              "module m;\n"
                              "  parameter P = `W + 1;\n"
                              "  logic [P-1:0] x;\n"
                              "endmodule\n"));
}

TEST(ExpressionPreprocessor, MacroExpandsToTernary) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`define PICK(c, a, b) ((c) ? (a) : (b))\n"
                              "module m;\n"
                              "  logic [7:0] x, y, z, w;\n"
                              "  initial x = `PICK(y > 0, z, w);\n"
                              "endmodule\n"));
}

TEST(ExpressionPreprocessor, PartSelectRangePassesThrough) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("module m;\n"
                              "  logic [15:0] data;\n"
                              "  logic [7:0] hi;\n"
                              "  initial hi = data[15:8];\n"
                              "endmodule\n"));
}

TEST(ExpressionPreprocessor, IndexedRangePlusPassesThrough) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("module m;\n"
                              "  logic [15:0] data;\n"
                              "  logic [7:0] hi;\n"
                              "  initial hi = data[0+:8];\n"
                              "endmodule\n"));
}

TEST(ExpressionPreprocessor, IndexedRangeMinusPassesThrough) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("module m;\n"
                              "  logic [15:0] data;\n"
                              "  logic [7:0] hi;\n"
                              "  initial hi = data[15-:8];\n"
                              "endmodule\n"));
}

TEST(ExpressionPreprocessor, MintypMaxInSpecparam) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("module m;\n"
                              "  specify\n"
                              "    specparam tRise = 1:2:3;\n"
                              "  endspecify\n"
                              "endmodule\n"));
}

TEST(ExpressionPreprocessor, ConstantParamExpressionDollar) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("module m;\n"
                              "  int q[$];\n"
                              "endmodule\n"));
}

TEST(ExpressionPreprocessor, ConditionalCompilationGuardsExpression) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`define USE_TERNARY\n"
                              "module m;\n"
                              "  logic [7:0] a, b, c, x;\n"
                              "`ifdef USE_TERNARY\n"
                              "  initial x = a ? b : c;\n"
                              "`else\n"
                              "  initial x = a + b + c;\n"
                              "`endif\n"
                              "endmodule\n"));
}

TEST(ExpressionPreprocessor, OperatorAssignmentInParensCrossLink) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("module m;\n"
                              "  integer x, y;\n"
                              "  initial x = (y += 1);\n"
                              "endmodule\n"));
}

TEST(ExpressionPreprocessor, GenvarExpressionPassesThrough) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i = i + 1) begin : gen\n"
      "    wire w;\n"
      "  end\n"
      "endmodule\n"));
}

}  // namespace
