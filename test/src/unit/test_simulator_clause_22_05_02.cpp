#include "helpers_preprocess_and_get.h"

TEST(UndefSimulation, UndefThenRedefineSimulatesNewValue) {
  auto result = PreprocessAndGet(
      "`define VAL 8'd10\n"
      "`undef VAL\n"
      "`define VAL 8'd77\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `VAL;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 77u);
}

TEST(UndefSimulation, UndefExcludesConditionalCodeFromSimulation) {
  auto result = PreprocessAndGet(
      "`define USE_ALT\n"
      "`undef USE_ALT\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "`ifdef USE_ALT\n"
      "  initial result = 8'd99;\n"
      "`else\n"
      "  initial result = 8'd11;\n"
      "`endif\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 11u);
}

TEST(UndefSimulation, UndefDoesNotAffectOtherMacroSimulation) {
  auto result = PreprocessAndGet(
      "`define A 8'd5\n"
      "`define B 8'd30\n"
      "`undef A\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `B;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 30u);
}
