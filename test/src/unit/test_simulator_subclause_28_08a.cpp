#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

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

TEST(BidirSwitchRun, ABitSelectTerminalConducts) {
  SimFixture f;
  auto out = RunCapture(
      "module top;\n"
      "  wire [1:0] v;\n"
      "  wire [3:0] w;\n"
      "  wire s1, s2, s3, s4;\n"
      "  logic c = 1, d = 1'bz;\n"
      "  assign v[0] = 1'b1;\n"
      "  assign w[2] = 1'b0;\n"
      "  assign s4 = d;\n"
      "  tran    t1 (v[0], s1);\n"
      "  tranif1 t2 (v[0], s2, c);\n"
      "  rtran   t3 (w[2], s3);\n"
      "  tran    t4 (w[1], s4);\n"
      "  initial begin\n"
      "    #1 $display(\"%b %b %b %b\", s1, s2, s3, w);\n"
      "    d = 1'b1;\n"
      "    #1 $display(\"%b\", w);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "1 1 0 z0zz\n"
            "z01z\n");
}

TEST(BidirSwitchRun, ASwitchJoiningTwoBitsOfOneNetConducts) {
  SimFixture f;
  auto out = RunCapture(
      "module top;\n"
      "  wire [2:0] v;\n"
      "  assign v[0] = 1'b1;\n"
      "  tran t (v[0], v[2]);\n"
      "  initial #1 $display(\"%b\", v);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1z1\n");
}

TEST(BidirSwitchRun, AChainThroughBitSelectTerminalsIsOneNetwork) {
  SimFixture f;
  auto out = RunCapture(
      "module top;\n"
      "  wire [1:0] v;\n"
      "  wire s, u, x;\n"
      "  assign u = 1'b1;\n"
      "  assign v[1] = 1'b0;\n"
      "  tran (v[0], s);\n"
      "  tran (s, u);\n"
      "  tran (v[1], x);\n"
      "  tran (x, s);\n"
      "  initial #1 $display(\"%b %b %b\", v, s, x);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "xx x x\n");
}

TEST(BidirSwitchRun, ASignalCrossesASwitchChainToABitSelectTerminal) {
  SimFixture f;
  auto out = RunCapture(
      "module top;\n"
      "  wire [1:0] v;\n"
      "  wire s, u;\n"
      "  assign u = 1'b1;\n"
      "  tran (v[0], s);\n"
      "  tran (s, u);\n"
      "  initial #1 $display(\"%b %b\", v, s);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "z1 1\n");
}

}  // namespace
