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

// §22.9: while `unconnected_drive pull1 is active, a child's unconnected input
// port is pulled high. Observe the pulled value reach the running design: the
// child selects on its unconnected input and drives the parent-visible result,
// which reads 1 only if the input was driven to 1 (an undriven input would
// evaluate to x and select 0 instead).
TEST(UnconnectedDriveSimulation, Pull1DrivesUnconnectedInputHighAtRuntime) {
  auto result = PreprocessAndGet(
      "`unconnected_drive pull1\n"
      "module child(input wire a, output logic [7:0] b);\n"
      "  assign b = a ? 8'd1 : 8'd0;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.b(result));\n"
      "endmodule\n",
      "result", CuPropagation::kUnconnectedDrive);
  EXPECT_EQ(result, 1u);
}

// §22.9: while `unconnected_drive pull0 is active, the unconnected input is
// pulled low. The child selects the nonzero arm only when its input is a known
// 0, so a runtime result of 1 confirms the port was driven to 0 (an undriven x
// input would select 0 here instead).
TEST(UnconnectedDriveSimulation, Pull0DrivesUnconnectedInputLowAtRuntime) {
  auto result = PreprocessAndGet(
      "`unconnected_drive pull0\n"
      "module child(input wire a, output logic [7:0] b);\n"
      "  assign b = a ? 8'd0 : 8'd1;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(.b(result));\n"
      "endmodule\n",
      "result", CuPropagation::kUnconnectedDrive);
  EXPECT_EQ(result, 1u);
}
