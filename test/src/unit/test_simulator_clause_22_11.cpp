#include "helpers_preprocess_and_get.h"

TEST(PragmaSimulation, MultiplePragmasSimulate) {
  auto result = PreprocessAndGet(
      "`pragma first_pragma\n"
      "module t;\n"
      "  `pragma second_pragma 42\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd77;\n"
      "endmodule\n"
      "`pragma third_pragma\n",
      "result");
  EXPECT_EQ(result, 77u);
}
