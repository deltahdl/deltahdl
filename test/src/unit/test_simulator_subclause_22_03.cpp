#include "helpers_preprocess_and_get.h"

TEST(ResetAllSimulation, PreservesMacroValuesForSimulation) {
  auto result = PreprocessAndGet(
      "`define CONST 8'd77\n"
      "`resetall\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `CONST;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 77u);
}

TEST(ResetAllSimulation, InsideExcludedBranchDoesNotAffectSimulation) {
  auto result = PreprocessAndGet(
      "`define VAL 8'd50\n"
      "`ifdef UNDEF\n"
      "`resetall\n"
      "`endif\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = `VAL;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 50u);
}
