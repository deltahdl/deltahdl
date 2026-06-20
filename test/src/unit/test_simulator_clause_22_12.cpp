#include "helpers_preprocess_and_get.h"

TEST(LineDirectiveSimulation, LineInsideModuleSimulatesCorrectly) {
  auto result = PreprocessAndGet(
      "module t;\n"
      "  `line 50 \"other.sv\" 0\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd42;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 42u);
}

TEST(LineDirectiveSimulation, LineBetweenModulesSimulatesCorrectly) {
  auto result = PreprocessAndGet(
      "module m1;\n"
      "  logic [7:0] unused;\n"
      "  initial unused = 8'd10;\n"
      "endmodule\n"
      "`line 100 \"switched.sv\" 0\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd55;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 55u);
}
