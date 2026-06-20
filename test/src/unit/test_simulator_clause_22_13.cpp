#include "helpers_preprocess_and_get.h"

TEST(FileAndLineMacroSimulation, LineExpandsToCorrectValue) {
  auto result = PreprocessAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  initial result = `__LINE__;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 3u);
}

TEST(FileAndLineMacroSimulation, LineValueDiffersPerLine) {
  auto result = PreprocessAndGet(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  logic [31:0] dummy;\n"
      "  initial begin\n"
      "    dummy = `__LINE__;\n"
      "    result = `__LINE__;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 6u);
}
