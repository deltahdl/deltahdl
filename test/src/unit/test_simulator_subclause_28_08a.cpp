#include <gtest/gtest.h>

#include <cstddef>
#include <iterator>
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

std::string CrossedStrengthsShown(const std::string& sw,
                                  const std::string& sources,
                                  const std::string& first,
                                  const std::string& second) {
  std::string ctl;
  if (sw == "tranif0") ctl = ", c0";
  if (sw == "tranif1") ctl = ", c1";
  std::string src = "module top;\n";
  src += sources;
  src += "  logic c0 = 0, c1 = 1;\n  ";
  src += sw;
  src += " t1 (";
  src += first;
  src += ctl;
  src += ");\n  ";
  src += sw;
  src += " t2 (";
  src += second;
  src += ctl;
  src +=
      ");\n"
      "  initial #1 $display(\"%v %v\", far1, far2);\n"
      "endmodule\n";
  SimFixture f;
  return RunCapture(src, f);
}

TEST(BidirSwitchRun, ASupplySourceCrossesAsStrongEitherWay) {
  for (const std::string& sw : {"tran", "tranif0", "tranif1"}) {
    EXPECT_EQ(CrossedStrengthsShown(sw,
                                    "  supply0 gnd;\n"
                                    "  supply1 vdd;\n"
                                    "  wire far1, far2;\n",
                                    "gnd, far1", "far2, vdd"),
              "St0 St1\n")
        << sw;
  }
}

TEST(BidirSwitchRun, AWeakSourceCrossesUnchanged) {
  for (const std::string& sw : {"tran", "tranif0", "tranif1"}) {
    EXPECT_EQ(CrossedStrengthsShown(sw,
                                    "  wire a, q, far1, far2;\n"
                                    "  assign (weak0, weak1) a = 1'b0;\n"
                                    "  assign (weak0, weak1) q = 1'b1;\n",
                                    "a, far1", "far2, q"),
              "We0 We1\n")
        << sw;
  }
}

TEST(BidirSwitchRun, EnabledSwitchesConductFromTheSecondTerminal) {
  SimFixture f;
  auto out = RunCapture(
      "module top;\n"
      "  wire a0, b0, a1, b1;\n"
      "  logic c0 = 0, c1 = 1;\n"
      "  assign b0 = 1'b1;\n"
      "  assign b1 = 1'b0;\n"
      "  tranif0 t0 (a0, b0, c0);\n"
      "  rtranif1 t1 (a1, b1, c1);\n"
      "  initial begin\n"
      "    #1 $display(\"%v %v\", a0, a1);\n"
      "    c0 = 1; c1 = 0;\n"
      "    #1 $display(\"%v %v\", a0, a1);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "St1 Pu0\n"
            "HiZ HiZ\n");
}

TEST(BidirSwitchRun, RtranConductsBothWaysAtReducedStrength) {
  SimFixture f;
  auto out = RunCapture(
      "module top;\n"
      "  wire a, b;\n"
      "  logic da = 1'bz, db = 1'bz;\n"
      "  assign a = da;\n"
      "  assign b = db;\n"
      "  rtran r1 (a, b);\n"
      "  initial begin\n"
      "    da = 1;\n"
      "    #1 $display(\"%v %v\", a, b);\n"
      "    da = 1'bz; db = 0;\n"
      "    #1 $display(\"%v %v\", a, b);\n"
      "    db = 1'bz;\n"
      "    #1 $display(\"%v %v\", a, b);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "St1 Pu1\n"
            "Pu0 St0\n"
            "HiZ HiZ\n");
}

TEST(BidirSwitchRun, Tranif0JoinsNetsOfAUserDefinedNetType) {
  SimFixture f;
  auto out = RunCapture(
      "module top;\n"
      "  nettype logic res_t;\n"
      "  res_t a, b;\n"
      "  logic c = 0;\n"
      "  assign a = 1'b1;\n"
      "  tranif0 t (a, b, c);\n"
      "  initial begin\n"
      "    #1 $display(\"b=%b\", b);\n"
      "    c = 1;\n"
      "    #1 $display(\"b=%b\", b);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "b=1\n"
            "b=z\n");
}

TEST(BidirSwitchRun, AnUnknownControlLeavesUserDefinedNetsApart) {
  for (const std::string& sw : {"tranif0", "tranif1"}) {
    const char* on = sw == "tranif0" ? "1'b0" : "1'b1";
    std::string src =
        "module top;\n"
        "  nettype logic res_t;\n"
        "  res_t a, b;\n"
        "  logic c = ";
    src += on;
    src += ";\n  assign a = 1'b1;\n  ";
    src += sw;
    src +=
        " t (a, b, c);\n"
        "  initial begin\n"
        "    #1 $write(\"%b \", b);\n"
        "    c = 1'bx;\n"
        "    #1 $write(\"%b \", b);\n"
        "    c = 1'bz;\n"
        "    #1 $display(\"%b\", b);\n"
        "  end\n"
        "endmodule\n";
    SimFixture f;
    EXPECT_EQ(RunCapture(src, f), "1 z z\n") << sw;
  }
}

TEST(BidirSwitchRun, AFourStateNetControlSwitchesTheSwitch) {
  SimFixture f;
  auto out = RunCapture(
      "module top;\n"
      "  wire a, b, en;\n"
      "  logic drive = 1;\n"
      "  assign en = drive;\n"
      "  assign a = 1'b1;\n"
      "  rtranif0 r (a, b, en);\n"
      "  initial begin\n"
      "    #1 $write(\"%b \", b);\n"
      "    drive = 0;\n"
      "    #1 $display(\"%b\", b);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "z 1\n");
}

TEST(BidirSwitchRun, DataCrossesADelayedSwitchWithoutDelay) {
  SimFixture f;
  auto out = RunCapture(
      "module top;\n"
      "  wire a, b;\n"
      "  logic c = 0, d = 0;\n"
      "  assign a = d;\n"
      "  tranif1 #(3, 5) t (a, b, c);\n"
      "  always @(b) $display(\"%0t b=%b\", $time, b);\n"
      "  initial begin\n"
      "    c = 1;\n"
      "    #10 d = 1;\n"
      "    #10 d = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "3 b=0\n"
            "10 b=1\n"
            "20 b=0\n");
}

TEST(BidirSwitchRun, OneDelayTimesTurningOnAndOff) {
  SimFixture f;
  auto out = RunCapture(
      "module top;\n"
      "  wire a, b;\n"
      "  logic c = 0;\n"
      "  assign a = 1'b1;\n"
      "  tranif1 #4 t (a, b, c);\n"
      "  always @(b) $display(\"%0t b=%b\", $time, b);\n"
      "  initial begin\n"
      "    #10 c = 1;\n"
      "    #10 c = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "14 b=1\n"
            "24 b=z\n");
}

TEST(BidirSwitchRun, AnUnknownControlTakesTheSmallerDelay) {
  const char* const kDelays[] = {"#(3, 5)", "#(5, 3)"};
  const char* const kExpected[] = {"13 b=x\n23 b=1\n33 b=x\n45 b=z\n",
                                   "13 b=x\n25 b=1\n33 b=x\n43 b=z\n"};
  for (std::size_t i = 0; i < std::size(kDelays); ++i) {
    std::string src =
        "module top;\n"
        "  wire a, b;\n"
        "  logic c = 0;\n"
        "  assign a = 1'b1;\n"
        "  tranif1 ";
    src += kDelays[i];
    src +=
        " t (a, b, c);\n"
        "  always @(b) $display(\"%0t b=%b\", $time, b);\n"
        "  initial begin\n"
        "    #10 c = 1'bx;\n"
        "    #10 c = 1;\n"
        "    #10 c = 1'bx;\n"
        "    #10 c = 0;\n"
        "  end\n"
        "endmodule\n";
    SimFixture f;
    EXPECT_EQ(RunCapture(src, f), kExpected[i]) << kDelays[i];
  }
}

TEST(BidirSwitchRun, EverySwitchKindRunsInAGenerateBlock) {
  SimFixture f;
  auto out = RunCapture(
      "module top;\n"
      "  wire [5:0] a, b;\n"
      "  logic c0 = 0, c1 = 1;\n"
      "  assign a = 6'b101101;\n"
      "  for (genvar k = 0; k < 1; k++) begin : g\n"
      "    tran t0 (a[0], b[0]);\n"
      "    rtran t1 (a[1], b[1]);\n"
      "  end\n"
      "  if (1) begin : h\n"
      "    tranif0 t2 (a[2], b[2], c0);\n"
      "    tranif1 t3 (a[3], b[3], c1);\n"
      "  end\n"
      "  case (1)\n"
      "    1: begin\n"
      "      rtranif0 t4 (a[4], b[4], c0);\n"
      "      rtranif1 t5 (a[5], b[5], c1);\n"
      "    end\n"
      "  endcase\n"
      "  initial #1 $display(\"%b\", b);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "101101\n");
}

}  // namespace
