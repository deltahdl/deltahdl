#include <gtest/gtest.h>

#include "fixture_simulator.h"
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

// §22.3 with §22.9: `resetall ends the `unconnected_drive pull1 for the module
// definitions after it, not for sub1 before it, whose unconnected input stays
// pulled to 1 while sub2's is an undriven net reading z. The `resetall reached
// back to sub1, which read x.
TEST(ResetAllSimulation, LeavesTheModulesBeforeItTheirUnconnectedDrive) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("`unconnected_drive pull1\n"
                                 "module sub1(input logic a, output logic b);\n"
                                 "  assign b = a;\n"
                                 "endmodule\n"
                                 "`resetall\n"
                                 "module sub2(input logic a, output logic b);\n"
                                 "  assign b = a;\n"
                                 "endmodule\n"
                                 "module t;\n"
                                 "  logic x, y;\n"
                                 "  sub1 s1(.b(x));\n"
                                 "  sub2 s2(.b(y));\n"
                                 "  initial #1 $display(\"%b %b\", x, y);\n"
                                 "endmodule\n",
                                 f),
            "1 z\n");
}
