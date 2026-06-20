#include "helpers_preprocess_and_get.h"

// §22.10 has no simulator-stage rule: the directives are consumed by the
// preprocessor and have no effect on simulation, so a cell module simulates
// like any other. One representative check is sufficient; the directive
// variations are observed in the preprocessor tests.
TEST(CelldefineSimulation, CelldefineModuleSimulatesCorrectly) {
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
