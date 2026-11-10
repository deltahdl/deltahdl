#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ParameterConstantSim, ByteLocalparamFromACharacterLiteralIsItsCode) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  localparam byte colon1 = \":\";\n"
                 "  initial $display(\"%0d %0d\", colon1, $bits(colon1));\n"
                 "endmodule\n",
                 f),
      "58 8\n");
}

TEST(ParameterConstantSim, LogicParameterFromALiteralIsOneBit) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  parameter logic flag = 1;\n"
                       "  initial $display(\"%0d %b\", $bits(flag), flag);\n"
                       "endmodule\n",
                       f),
            "1 1\n");
}

}  // namespace
