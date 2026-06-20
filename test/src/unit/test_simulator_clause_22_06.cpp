#include "helpers_preprocess_and_get.h"

TEST(IfdefSimulation, IfdefSelectsValueForSimulation) {
  auto result = PreprocessAndGet(
      "`define USE_ALT\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "`ifdef USE_ALT\n"
      "  initial result = 8'd77;\n"
      "`else\n"
      "  initial result = 8'd11;\n"
      "`endif\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 77u);
}

TEST(IfdefSimulation, IfdefElseBranchSimulatesWhenUndefined) {
  auto result = PreprocessAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "`ifdef USE_ALT\n"
      "  initial result = 8'd77;\n"
      "`else\n"
      "  initial result = 8'd11;\n"
      "`endif\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 11u);
}

TEST(IfdefSimulation, ElsifChainSelectsCorrectValueForSimulation) {
  auto result = PreprocessAndGet(
      "`define MODE_C\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "`ifdef MODE_A\n"
      "  initial result = 8'd1;\n"
      "`elsif MODE_B\n"
      "  initial result = 8'd2;\n"
      "`elsif MODE_C\n"
      "  initial result = 8'd3;\n"
      "`else\n"
      "  initial result = 8'd4;\n"
      "`endif\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 3u);
}

TEST(IfdefSimulation, IfndefSimulatesWhenUndefined) {
  auto result = PreprocessAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "`ifndef MISSING\n"
      "  initial result = 8'd55;\n"
      "`else\n"
      "  initial result = 8'd0;\n"
      "`endif\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 55u);
}
