#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §28.8 (printed page 840): both bidirectional terminals always carry signals
// into and out of the device, in either direction, so a tran carries whichever
// side is driven to the other, and neither side once nothing drives either.
TEST(BidirSwitchRun, TranConductsInBothDirections) {
  SimFixture f;
  auto out = RunCapture(
      "module top;\n"
      "  wire a, b;\n"
      "  logic da = 1'bz, db = 1'bz;\n"
      "  assign a = da;\n"
      "  assign b = db;\n"
      "  tran t1 (a, b);\n"
      "  initial begin\n"
      "    da = 1;\n"
      "    #1 $display(\"a=%b b=%b\", a, b);\n"
      "    da = 1'bz; db = 0;\n"
      "    #1 $display(\"a=%b b=%b\", a, b);\n"
      "    db = 1'bz;\n"
      "    #1 $display(\"a=%b b=%b\", a, b);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "a=1 b=1\n"
            "a=0 b=0\n"
            "a=z b=z\n");
}

// §28.8: a tranif1 conducts while its control is 1 and a tranif0 while it is
// 0, each blocking otherwise; with the control x, §4.9.5 (printed page 71) has
// the network solved "with these transistors set to all possible combinations
// of fully conducting and nonconducting", and a node with no "unique logic
// level in all cases" -- 1 when on, z when off -- is x.
TEST(BidirSwitchRun, TranifFollowsItsControl) {
  SimFixture f;
  auto out = RunCapture(
      "module top;\n"
      "  wire a, b1, b0;\n"
      "  logic c = 1, src = 1;\n"
      "  assign a = src;\n"
      "  tranif1 t1 (a, b1, c);\n"
      "  tranif0 t0 (a, b0, c);\n"
      "  initial begin\n"
      "    #1 $display(\"b1=%b b0=%b\", b1, b0);\n"
      "    c = 0;\n"
      "    #1 $display(\"b1=%b b0=%b\", b1, b0);\n"
      "    c = 1'bx;\n"
      "    #1 $display(\"b1=%b b0=%b\", b1, b0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "b1=1 b0=z\n"
            "b1=z b0=1\n"
            "b1=x b0=x\n");
}

// §28.8: the control input is a 4-state net, a 4-state variable or a 2-state
// variable. A bit control turns the switch on and off as a logic one does.
TEST(BidirSwitchRun, TranifControlMayBeATwoStateVariable) {
  SimFixture f;
  auto out = RunCapture(
      "module top;\n"
      "  wire a, b;\n"
      "  bit c = 1;\n"
      "  assign a = 1'b1;\n"
      "  tranif1 t1 (a, b, c);\n"
      "  initial begin\n"
      "    #1 $display(\"b=%b\", b);\n"
      "    c = 0;\n"
      "    #1 $display(\"b=%b\", b);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "b=1\n"
            "b=z\n");
}

// §28.8: the first delay is the control input's turn-on delay and the second
// its turn-off delay, with no delay through the terminals themselves: a tranif1
// #(3, 5) turned on at 0, off at 4 and on again at 10 passes its driven side at
// 3, stops at 9 and passes again at 13.
TEST(BidirSwitchRun, TranifTurnsOnAndOffAfterItsDelays) {
  SimFixture f;
  auto out = RunCapture(
      "module top;\n"
      "  wire a, b;\n"
      "  logic c = 0;\n"
      "  assign a = 1'b1;\n"
      "  tranif1 #(3, 5) t1 (a, b, c);\n"
      "  always @(b) $display(\"t=%0t b=%b\", $time, b);\n"
      "  initial begin\n"
      "    c = 1;\n"
      "    #4 c = 0;\n"
      "    #6 c = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "t=3 b=1\n"
            "t=9 b=z\n"
            "t=13 b=1\n");
}

// §28.13 and §28.14 (printed page 855): a tran, tranif0 or tranif1 passes a
// signal's strength but for supply, which it reduces to strong, and an rtran
// or rtranif1 reduces it by Table 28-8 -- strong to pull, pull to weak.
TEST(BidirSwitchRun, SwitchesPassOrReduceStrength) {
  SimFixture f;
  auto out = RunCapture(
      "module top;\n"
      "  supply1 vdd;\n"
      "  wire a, b, c, d;\n"
      "  wire pd, st;\n"
      "  pulldown (pd);\n"
      "  assign st = 1'b1;\n"
      "  logic on = 1;\n"
      "  tran t1 (vdd, a);\n"
      "  rtran t2 (st, b);\n"
      "  rtranif1 t3 (pd, c, on);\n"
      "  tranif0 t4 (st, d, ~on);\n"
      "  initial #1 $display(\"a=%b %v b=%b %v c=%b %v d=%b %v\", a, a, b, b, "
      "c, c, d, d);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "a=1 St1 b=1 Pu1 c=0 We0 d=1 St1\n");
}

// §28.8: switches in series join every net along them, a resistive one
// reducing the strength at each crossing, and the nets a tran joins resolve
// their drivers together (§28.12.1), the pull 1 overcoming the weak 0 on both
// sides; a tran inside an instance joins the nets its ports are connected
// to.
TEST(BidirSwitchRun, SwitchesChainAndResolveTheirNetsTogether) {
  SimFixture f;
  auto out = RunCapture(
      "module swcell (inout p, q);\n"
      "  tran t (p, q);\n"
      "endmodule\n"
      "module top;\n"
      "  wire a, b, c, d, e, f, g, h, m, n;\n"
      "  assign a = 1'b1;\n"
      "  tran t1 (a, b);\n"
      "  tran t2 (b, c);\n"
      "  assign d = 1'b1;\n"
      "  rtran r1 (d, e);\n"
      "  rtran r2 (e, f);\n"
      "  assign (weak0, weak1) g = 1'b0;\n"
      "  assign (pull0, pull1) h = 1'b1;\n"
      "  tran t3 (g, h);\n"
      "  assign m = 1'b0;\n"
      "  swcell u (m, n);\n"
      "  initial #1 $display(\"c=%v f=%v g=%v h=%v n=%v\", c, f, g, h, n);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "c=St1 f=We1 g=Pu1 h=Pu1 n=St0\n");
}

// §28.8: tran, tranif1 and tranif0 devices may be connected to nets of
// user-defined net types as well, and such a switch passes the value while it
// conducts.
TEST(BidirSwitchRun, TranifJoinsNetsOfAUserDefinedNetType) {
  SimFixture f;
  auto out = RunCapture(
      "module top;\n"
      "  nettype logic res_t;\n"
      "  res_t a, b;\n"
      "  logic c = 1;\n"
      "  assign a = 1'b1;\n"
      "  tranif1 t (a, b, c);\n"
      "  initial #1 $display(\"b=%b\", b);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "b=1\n");
}

}  // namespace
