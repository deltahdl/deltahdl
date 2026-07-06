#include "helpers_preprocess_and_get.h"

TEST(DefaultNettypeSimulation, WireModuleSimulatesCorrectly) {
  auto result = PreprocessAndGet(
      "`default_nettype wire\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd42;\n"
      "endmodule\n",
      "result", CuPropagation::kDefaultNetType);
  EXPECT_EQ(result, 42u);
}
