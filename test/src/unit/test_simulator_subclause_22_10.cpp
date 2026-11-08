#include <gtest/gtest.h>

#include "helpers_preprocess_and_get.h"

TEST(CelldefineSimulation, CellModuleRunsUnchanged) {
  auto result = PreprocessAndGet(
      "`celldefine\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd42;\n"
      "endmodule\n"
      "`endcelldefine\n",
      "result");
  EXPECT_EQ(result, 42u);
}

TEST(CelldefineSimulation, DirectivesInsideModuleBodyRunUnchanged) {
  auto result = PreprocessAndGet(
      "module t;\n"
      "`celldefine\n"
      "  logic [7:0] result;\n"
      "`endcelldefine\n"
      "  initial result = 8'd17;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 17u);
}

TEST(CelldefineSimulation, ResetallBetweenModulesRunsUnchanged) {
  auto result = PreprocessAndGet(
      "`celldefine\n"
      "module cell_mod;\n"
      "  logic [7:0] spare;\n"
      "  initial spare = 8'd1;\n"
      "endmodule\n"
      "`resetall\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd21 + 8'd21;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 42u);
}

TEST(CelldefineSimulation, DirectivesInsideProceduralBlockRunUnchanged) {
  auto result = PreprocessAndGet(
      "`celldefine\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "`endcelldefine\n"
      "    result = 8'd5;\n"
      "    result = result + 8'd3;\n"
      "`celldefine\n"
      "  end\n"
      "endmodule\n"
      "`endcelldefine\n",
      "result");
  EXPECT_EQ(result, 8u);
}
