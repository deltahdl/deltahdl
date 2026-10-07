#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

// §30.4.3 states two simulator-stage rules for edge-sensitive module
// paths: when a vector port is the source, the edge transition is detected on
// the LSB; and when no edge identifier is given, the path is active on any
// transition. Neither has a production carrier yet -- module path delays are
// not lowered into the scheduler (the lowerer holds no specify references, and
// simulator/specify.cpp handles only system timing checks). This single smoke
// test therefore confirms that an edge-sensitive specify path does not disturb
// the rest of simulation; it does not observe LSB edge detection or the
// any-transition default, since no production code applies them.
namespace {

TEST(SpecifyPathSim, EdgeSensitivePathSimulates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    (posedge clk => q) = 5;\n"
      "  endspecify\n"
      "  initial x = 8'd33;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 33u);
}

// A gate `y = <body>` from clk and d whose specify block is `paths`, driven by
// the steps in `stimulus` after clk = <clk0> and d = 1, printing each change of
// y from 8 on.
std::string EdgePathDesign(const std::string& clk_decl, const std::string& body,
                           const std::string& paths, const std::string& clk0,
                           const std::string& stimulus) {
  return "module mygate(input " + clk_decl +
         "clk, input d, output y);\n"
         "  assign y = " +
         body +
         ";\n"
         "  specify\n" +
         paths +
         "  endspecify\n"
         "endmodule\n"
         "module top;\n"
         "  logic " +
         clk_decl +
         "clk;\n"
         "  logic d;\n"
         "  wire ty;\n"
         "  mygate u(.clk(clk), .d(d), .y(ty));\n"
         "  always @(ty) if ($time >= 8) $display(\"t=%0t y=%b\", $time, ty);\n"
         "  initial begin\n"
         "    clk = " +
         clk0 + "; d = 1;\n" + stimulus +
         "  end\n"
         "endmodule\n";
}

// §30.4.3 (printed page 874): an edge-sensitive path models input-to-output
// delays that happen only when the named edge appears on the source signal, so
// beside `(negedge clk => (y : d)) = (1, 2)` a rising clk takes the posedge
// path's rise 3 and a falling one the negedge path's fall 2. The negedge path's
// rise 1 was taken at the rising edge.
TEST(EdgeSensitivePathRun, EachEdgeTakesItsOwnPath) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(EdgePathDesign("", "clk & d",
                                "    (posedge clk => (y : d)) = (3, 5);\n"
                                "    (negedge clk => (y : d)) = (1, 2);\n",
                                "0",
                                "    #10 clk = 1;\n"
                                "    #10 clk = 0;\n"),
                 f),
      "t=13 y=1\nt=22 y=0\n");
}

// The same on logic that inverts clk, as §30.4.3 Example 2's negative polarity
// describes: the falling clk raises y through the negedge path's rise 4, the
// rising one lowers it through the posedge path's fall 2.
TEST(EdgeSensitivePathRun, InvertingLogicTakesThePathOfTheEdgeThatOccurred) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(EdgePathDesign("", "~clk & d",
                                "    (negedge clk => (y -: d)) = (4, 6);\n"
                                "    (posedge clk => (y -: d)) = (1, 2);\n",
                                "1",
                                "    #10 clk = 0;\n"
                                "    #10 clk = 1;\n"),
                 f),
      "t=14 y=1\nt=22 y=0\n");
}

// §30.4.3: when the input terminal descriptor names a vector port, the edge is
// detected on its LSB. 2'b10 to 2'b11 is a posedge of the LSB (rise 5), 2'b01
// to 2'b00 a negedge (fall 2), and the changes of the other bit are edges of
// neither.
TEST(EdgeSensitivePathRun, VectorSourceEdgeIsDetectedOnItsLsb) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(EdgePathDesign("[1:0] ", "clk[0] & d",
                                "    (posedge clk => (y : d)) = (5, 5);\n"
                                "    (negedge clk => (y : d)) = (2, 2);\n",
                                "2'b00",
                                "    #10 clk = 2'b10;\n"
                                "    #10 clk = 2'b11;\n"
                                "    #10 clk = 2'b01;\n"
                                "    #10 clk = 2'b00;\n"),
                 f),
      "t=25 y=1\nt=42 y=0\n");
}

// A path from a bit-select of the vector detects the edge on that bit: clk[1]
// rising at 10 takes the posedge path's 5, falling at 30 the negedge path's 2.
TEST(EdgeSensitivePathRun, SelectSourceEdgeIsDetectedOnTheSelectedBit) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(EdgePathDesign("[1:0] ", "clk[1] & d",
                                "    (posedge clk[1] => (y : d)) = (5, 5);\n"
                                "    (negedge clk[1] => (y : d)) = (2, 2);\n",
                                "2'b00",
                                "    #10 clk = 2'b10;\n"
                                "    #10 clk = 2'b11;\n"
                                "    #10 clk = 2'b01;\n"
                                "    #10 clk = 2'b00;\n"),
                 f),
      "t=15 y=1\nt=32 y=0\n");
}

// §30.4.4.3 Example 3 (printed page 878) with a negedge path beside it: the
// posedge paths under `reset` (15, 8) and under `!reset && cntrl` (6, 2) govern
// the rising edges by their conditions, and the unconditional negedge path's
// fall 2 the falling ones; its rise 8 was taken at both rising edges.
TEST(EdgeSensitivePathRun, ConditionalEdgePathsBesideAnOtherEdgePath) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module mygate(input clk, input data, input reset, input cntrl,\n"
          "              output q);\n"
          "  assign q = clk & data;\n"
          "  specify\n"
          "    if (reset) (posedge clk => (q : data)) = (15, 8);\n"
          "    if (!reset && cntrl) (posedge clk => (q : data)) = (6, 2);\n"
          "    (negedge clk => (q : data)) = (8, 2);\n"
          "  endspecify\n"
          "endmodule\n"
          "module top;\n"
          "  logic clk, data, reset, cntrl;\n"
          "  wire tq;\n"
          "  mygate u(.clk(clk), .data(data), .reset(reset), .cntrl(cntrl),\n"
          "           .q(tq));\n"
          "  always @(tq) if ($time >= 8) $display(\"t=%0t q=%b\", $time, "
          "tq);\n"
          "  initial begin\n"
          "    clk = 0; data = 1; reset = 1; cntrl = 0;\n"
          "    #10 clk = 1;\n"
          "    #20 begin clk = 0; reset = 0; cntrl = 1; end\n"
          "    #10 clk = 1;\n"
          "    #10 clk = 0;\n"
          "  end\n"
          "endmodule\n",
          f),
      "t=25 q=1\nt=32 q=0\nt=46 q=1\nt=52 q=0\n");
}

}  // namespace
