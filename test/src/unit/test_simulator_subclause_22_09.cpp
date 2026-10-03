#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
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

// A module `name` passing its unconnected-to-be input a to its output b.
static std::string PassThrough(const std::string& name) {
  return "module " + name +
         "(input logic a, output logic b);\n"
         "  assign b = a;\n"
         "endmodule\n";
}

// §22.9: `unconnected_drive governs the module definitions that follow it, so
// a `pull0` after the last module leaves sub's unconnected input pulled to 1.
// The trailing directive governed every module, and b read 0.
TEST(UnconnectedDriveSimulation, ATrailingDirectiveLeavesTheModulesBeforeIt) {
  SimFixture f;
  EXPECT_EQ(
      PreprocessAndCapture("`unconnected_drive pull1\n" + PassThrough("sub") +
                               "module t;\n"
                               "  logic b;\n"
                               "  sub s(.b(b));\n"
                               "  initial #1 $display(\"%b\", b);\n"
                               "endmodule\n"
                               "`unconnected_drive pull0\n",
                           f),
      "1\n");
}

// §22.9 with §23.3.3.3: the drive in force at each child's definition is the
// one its unconnected input takes, whatever is in force at the instantiating
// t: sub1's pulls to 1, sub2's, under `nounconnected_drive, is an undriven net
// reading z, and sub3's pulls to 0. The last directive governed all three,
// which read x x x.
TEST(UnconnectedDriveSimulation, EachChildTakesTheDriveAtItsDefinition) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture(
                "`unconnected_drive pull1\n" + PassThrough("sub1") +
                    "`nounconnected_drive\n" + PassThrough("sub2") +
                    "`unconnected_drive pull0\n" + PassThrough("sub3") +
                    "`nounconnected_drive\n"
                    "module t;\n"
                    "  logic x, y, z;\n"
                    "  sub1 s1(.b(x));\n"
                    "  sub2 s2(.b(y));\n"
                    "  sub3 s3(.b(z));\n"
                    "  initial #1 $display(\"%b %b %b\", "
                    "x, y, z);\n"
                    "endmodule\n",
                f),
            "1 z 0\n");
}
