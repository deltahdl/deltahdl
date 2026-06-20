#include "helpers_preprocess_and_get.h"

TEST(UndefineAllSimulation, UndefineAllThenRedefineSimulatesNewValue) {
  auto result = PreprocessAndGet(
      "`define VAL 8'd10\n"
      "`undefineall\n"
      "`define VAL 8'd55\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `VAL;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 55u);
}

TEST(UndefineAllSimulation, UndefineAllExcludesConditionalFromSimulation) {
  auto result = PreprocessAndGet(
      "`define USE_ALT\n"
      "`undefineall\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "`ifdef USE_ALT\n"
      "  initial result = 8'd99;\n"
      "`else\n"
      "  initial result = 8'd22;\n"
      "`endif\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 22u);
}
