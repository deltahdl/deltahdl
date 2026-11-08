#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(GateNetDelays, ANetDelayIsChosenFromTheNetsResolvedTransition) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  reg a = 1, b = 1;\n"
      "  wire #(2, 8) w;\n"
      "  assign w = a;\n"
      "  assign w = b;\n"
      "  initial begin\n"
      "    #10 a = 0;\n"
      "    #3 $display(\"%b\", w);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "x\n");
}

TEST(GateNetDelays, ADriversDelayAndTheNetDelayFollowOneAnother) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  reg a = 0;\n"
      "  wire #4 w;\n"
      "  assign #3 w = a;\n"
      "  initial begin\n"
      "    #10 a = 1;\n"
      "    #6 $display(\"%b\", w);\n"
      "    #1 $display(\"%b\", w);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "0\n"
            "1\n");
}

TEST(GateNetDelays, AForcedDelayedNetHoldsAndIsReleased) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  reg a = 0;\n"
      "  wire #5 w;\n"
      "  assign w = a;\n"
      "  initial begin\n"
      "    #10 force w = 1'b1;\n"
      "    #1 a = 1;\n"
      "    #1 a = 0;\n"
      "    #1 $display(\"%b\", w);\n"
      "    release w;\n"
      "    #10 $display(\"%b\", w);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "1\n"
            "0\n");
}

TEST(GateNetDelays, ADelayedNetJoinedByASwitchTakesTheCarriedValue) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  wire #3 w;\n"
      "  wire x;\n"
      "  assign x = 1'b1;\n"
      "  tran (w, x);\n"
      "  initial #10 $display(\"%b\", w);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1\n");
}

}  // namespace
