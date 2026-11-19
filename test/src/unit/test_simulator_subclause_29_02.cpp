#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(UdpHighImpedanceInput, AZOnACombinationalInputSelectsTheXRow) {
  SimFixture f;
  auto out = RunCapture(
      "primitive p(output y, input a, input b);\n"
      "  table\n"
      "    x 0 : 1;\n"
      "    0 0 : 0;\n"
      "    1 0 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  reg a = 1'bz, b = 0;\n"
      "  wire y;\n"
      "  p u(y, a, b);\n"
      "  initial #1 $display(\"%v\", y);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "St1\n");
}

TEST(UdpHighImpedanceInput, AZOnALevelSensitiveInputSelectsTheXRow) {
  SimFixture f;
  auto out = RunCapture(
      "primitive p(output reg q, input d, input en);\n"
      "  table\n"
      "    x 0 : ? : 1;\n"
      "    0 0 : ? : 0;\n"
      "    1 0 : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  reg d = 1'bz, en = 0;\n"
      "  wire q;\n"
      "  p u(q, d, en);\n"
      "  initial #1 $display(\"%v\", q);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "St1\n");
}

TEST(UdpHighImpedanceInput, AnUnlistedAllZInputDrivesXNeverZ) {
  SimFixture f;
  auto out = RunCapture(
      "primitive p(output y, input a);\n"
      "  table\n"
      "    0 : 0;\n"
      "    1 : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  reg a = 1'bz;\n"
      "  wire y;\n"
      "  p u(y, a);\n"
      "  initial #1 $display(\"%v\", y);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "StX\n");
}

}  // namespace
