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

std::string EveryTransitionTimed(const std::string& declaration) {
  SimFixture f;
  return RunCapture(
      "module m;\n"
      "  reg v, en;\n"
      "  " +
          declaration +
          "\n"
          "  initial begin\n"
          "    $monitor(\"%0t %b\", $time, w);\n"
          "    v = 0; en = 1;\n"
          "    #50 v = 1; #50 v = 1'bx; #50 en = 0; #50 v = 0; en = 1;\n"
          "    #50 v = 1'bx; #50 v = 1; #50 en = 0; #50 v = 1; en = 1;\n"
          "    #50 v = 0; #50 en = 0; #50 v = 1'bx; en = 1; #50 v = 0;\n"
          "    #50 $finish;\n"
          "  end\n"
          "endmodule\n",
      f);
}

struct TimedTransitionRow {
  const char* delay;
  const char* landings;
};

constexpr TimedTransitionRow kTimedTransitionRows[] = {
    {"#5",
     "5 0 55 1 105 x 155 z 205 0 255 x 305 1 355 z 405 1 455 0 505 z "
     "555 x 605 0 "},
    {"#(7,11)",
     "11 0 57 1 107 x 157 z 211 0 257 x 307 1 357 z 407 1 461 0 "
     "507 z 557 x 611 0 "},
    {"#(11,7)",
     "7 0 61 1 107 x 157 z 207 0 257 x 311 1 357 z 411 1 457 0 "
     "507 z 557 x 607 0 "},
    {"#(7,11,15)",
     "11 0 57 1 107 x 165 z 211 0 257 x 307 1 365 z 407 1 "
     "461 0 515 z 557 x 611 0 "},
    {"#(15,11,7)",
     "11 0 65 1 107 x 157 z 211 0 257 x 315 1 357 z 415 1 "
     "461 0 507 z 557 x 611 0 "},
    {"#(11,15,7)",
     "15 0 61 1 107 x 157 z 215 0 257 x 311 1 357 z 411 1 "
     "465 0 507 z 557 x 615 0 "},
};

std::string LandingsAfterTimeZero(const std::string& trace) {
  std::string flat;
  for (char c : trace) flat += c == '\n' ? ' ' : c;
  auto first = flat.find(' ', flat.find(' ') + 1);
  auto finish = flat.find("$finish");
  return flat.substr(first + 1, finish - first - 1);
}

TEST(GateNetDelays, EveryNetTransitionLandsAtTheDelayOfItsTableRow) {
  for (const auto& row : kTimedTransitionRows) {
    std::string decl =
        std::string("wire ") + row.delay + " w; assign w = en ? v : 1'bz;";
    auto trace = EveryTransitionTimed(decl);
    EXPECT_EQ(trace.substr(0, 4), "0 z\n") << decl;
    EXPECT_EQ(LandingsAfterTimeZero(trace), row.landings) << decl;
  }
}

TEST(GateNetDelays, EveryThreeStateGateTransitionLandsAtItsTableRowDelay) {
  for (const auto& row : kTimedTransitionRows) {
    std::string decl =
        std::string("wire w; bufif1 ") + row.delay + " g(w, v, en);";
    auto trace = EveryTransitionTimed(decl);
    EXPECT_EQ(trace.substr(0, 4), "0 x\n") << decl;
    EXPECT_EQ(LandingsAfterTimeZero(trace), row.landings) << decl;
  }
}

TEST(GateNetDelays, ASingleDelayTimesAThreeStateGatesAmbiguousLevels) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  reg d, en;\n"
      "  wire y;\n"
      "  bufif1 #5 g(y, d, en);\n"
      "  initial begin\n"
      "    $monitor(\"%0t %v\", $time, y);\n"
      "    d = 0; en = 1;\n"
      "    #50 d = 1; en = 1'bx;\n"
      "    #50 en = 0;\n"
      "    #50 d = 0; en = 1'bx;\n"
      "    #50 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "0 StX\n5 St0\n55 StH\n105 HiZ\n155 StL\n$finish at time 200\n");
}

TEST(GateNetDelays, AGateDelayTimesEveryOneOfItsOutputs) {
  SimFixture f;
  auto out = RunCapture(
      "module m;\n"
      "  reg a;\n"
      "  wire y1, y2, y3;\n"
      "  buf #(7,11) g(y1, y2, y3, a);\n"
      "  initial begin\n"
      "    $monitor(\"%0t %b%b%b\", $time, y1, y2, y3);\n"
      "    a = 0; #50 a = 1; #50 a = 0; #50 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0 xxx\n11 000\n57 111\n111 000\n$finish at time 150\n");
}

TEST(GateNetDelays, DelaysAccumulateAlongEveryGateOfALatchPath) {
  SimFixture f;
  auto out = RunCapture(
      "module tri_latch (qout, nqout, clock, data, enable);\n"
      "  output qout, nqout;\n"
      "  input clock, data, enable;\n"
      "  tri qout, nqout;\n"
      "  not #5 n1 (ndata, data);\n"
      "  nand #(3,5) n2 (wa, data, clock), n3 (wb, ndata, clock);\n"
      "  nand #(12,15) n4 (q, nq, wa), n5 (nq, q, wb);\n"
      "  bufif1 #(3,7,13) q_drive (qout, q, enable),\n"
      "                   nq_drive (nqout, nq, enable);\n"
      "endmodule\n"
      "module m;\n"
      "  reg clock, data, enable;\n"
      "  wire qout, nqout;\n"
      "  tri_latch l(qout, nqout, clock, data, enable);\n"
      "  initial begin\n"
      "    $monitor(\"%0t %b%b\", $time, qout, nqout);\n"
      "    clock = 0; data = 0; enable = 1;\n"
      "    #100 clock = 1; #100 clock = 0; #100 data = 1;\n"
      "    #100 clock = 1; #100 enable = 0; #100 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "0 xx\n120 x1\n139 01\n420 11\n439 10\n513 zz\n"
            "$finish at time 600\n");
}

TEST(GateNetDelays, ANetDelayInAnInterfaceTimesItsContinuousAssignment) {
  SimFixture f;
  auto out = RunCapture(
      "interface bus;\n"
      "  logic v;\n"
      "  wire #(7,11) w;\n"
      "  assign w = v;\n"
      "endinterface\n"
      "module m;\n"
      "  bus b();\n"
      "  initial begin\n"
      "    b.v = 0; #50 b.v = 1;\n"
      "    #6 $write(\"%b\", b.w); #1 $write(\"%b\", b.w);\n"
      "    #43 b.v = 0;\n"
      "    #10 $write(\"%b\", b.w); #1 $display(\"%b\", b.w);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0110\n");
}

}  // namespace
