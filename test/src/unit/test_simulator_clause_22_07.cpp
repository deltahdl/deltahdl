#include "helpers_preprocess_and_get.h"

TEST(TimescaleSimulation, TimescaleModuleSimulatesCorrectly) {
  auto result = PreprocessAndGet(
      "`timescale 1ns / 1ps\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd42;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 42u);
}

TEST(TimescaleSimulation, MultipleTimescaleModulesSimulate) {
  auto result = PreprocessAndGet(
      "`timescale 1ns / 1ps\n"
      "module m1;\n"
      "  logic [7:0] unused;\n"
      "  initial unused = 8'd10;\n"
      "endmodule\n"
      "`timescale 1us / 1ns\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd77;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 77u);
}

TEST(TimescaleSimulation, LaterTimescaleOverrideSimulates) {
  auto result = PreprocessAndGet(
      "`timescale 1ns / 1ps\n"
      "`timescale 10us / 1us\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd99;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 99u);
}
