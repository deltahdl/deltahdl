#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §28.16 makes a net delay the time from a driver of the net changing to the
// net taking the value its drivers resolve to, chosen by Table 28-9 from the
// net's own transition: a falls at 10, the net goes from 1 to x, and the
// lesser delay of 2 brings the x at 12. Given to each driver and chosen from
// a's own fall, the delay was 8 and the net still read 1 at 13.
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

// A driver with a delay of its own and a net delay are two segments of one
// path (§10.3.3): the driver's 3, then the net's 4, so a's rise at 10 reaches
// w at 17 and not before.
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

// §10.6.2: a force on a delayed net holds it against its driver, and after the
// release the net goes on to the value its driver resolves to.
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

// A delayed net joined to another by a switch takes the value the switch
// carries to it.
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
