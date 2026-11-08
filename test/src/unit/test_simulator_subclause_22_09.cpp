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

static std::string PassThrough(const std::string& name) {
  return "module " + name +
         "(input logic a, output logic b);\n"
         "  assign b = a;\n"
         "endmodule\n";
}

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
