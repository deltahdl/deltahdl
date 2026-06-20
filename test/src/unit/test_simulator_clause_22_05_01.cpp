#include "helpers_preprocess_and_get.h"

TEST(DefineSimulation, ObjectLikeMacroSimulatesCorrectly) {
  auto result = PreprocessAndGet(
      "`define VAL 8'd99\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `VAL;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 99u);
}

TEST(DefineSimulation, FunctionLikeMacroSimulatesCorrectly) {
  auto result = PreprocessAndGet(
      "`define DOUBLE(x) (x * 2)\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `DOUBLE(8'd7);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 14u);
}

TEST(DefineSimulation, RedefinedMacroUsesLatestValueForSimulation) {
  auto result = PreprocessAndGet(
      "`define V 8'd10\n"
      "`define V 8'd25\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `V;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 25u);
}

TEST(DefineSimulation, NestedMacroSimulatesCorrectly) {
  auto result = PreprocessAndGet(
      "`define INNER 8'd4\n"
      "`define OUTER (`INNER + 8'd6)\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `OUTER;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 10u);
}

TEST(DefineSimulation, MacroWithDefaultArgSimulatesCorrectly) {
  auto result = PreprocessAndGet(
      "`define ADD(a, b=8'd50) (a + b)\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `ADD(8'd3);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 53u);
}
