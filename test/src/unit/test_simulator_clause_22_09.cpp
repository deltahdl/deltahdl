#include "helpers_preprocess_and_get.h"

TEST(UnconnectedDriveSimulation, Pull1ModuleSimulatesCorrectly) {
  auto result = PreprocessAndGet(
      "`unconnected_drive pull1\n"
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 8'd10;\n"
      "endmodule\n"
      "`nounconnected_drive\n",
      "result", CuPropagation::kUnconnectedDrive);
  EXPECT_EQ(result, 10u);
}
