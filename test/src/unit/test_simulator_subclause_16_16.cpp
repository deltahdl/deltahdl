#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// A design around the module given, as test/src/e2e/clock_resolution.sv
// is: the top t drives clk rising at 5, 15, 25 and 35 and falling at 10,
// 20, 30 and 40, a 1 across the ticks of 15 and 20 and b across those of
// 25 and 30, and instantiates the module as u1; the run ends at 40. An
// attempt of a |=> !b at 15 fails at 25 and one at 20 at 30, and a ##1 b
// matches from 15 at 25 and from 20 at 30, so the time an assertion
// reports names its clock: 25 for posedge clk and 30 for negedge.
std::string Design(const std::string& module) {
  return module +
         "module t;\n"
         "  logic clk = 0;\n"
         "  logic a = 0, b = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  m u1(a, b, clk);\n"
         "  initial begin\n"
         "    #12 a = 1;\n"
         "    #10 a = 0; b = 1;\n"
         "    #12 b = 0;\n"
         "    #6 $finish;\n"
         "  end\n"
         "endmodule\n";
}

// §16.16 (a), (b), (c) and (d): under a default clocking of posedge clk,
// the instance of the unclocked q1 and the unclocked spec take the default,
// the spec written with negedge clk its own, the instance of the clocking
// block's q3 the block's, and the instance of q5 the clock q5 declares; in
// the always at negedge clk the instance of q1 takes the inferred negedge
// over the default and the instance of posedge_clk.q3 is queued at negedge
// clk and checked at the next posedge.
TEST(ClockResolutionRun, EachRuleClocksItsStatement) {
  SimFixture f;
  std::string out = RunCapture(
      Design(
          "module m(input logic a, b, clk);\n"
          "  property q1;\n"
          "    a |=> !b;\n"
          "  endproperty\n"
          "  default clocking posedge_clk @(posedge clk);\n"
          "    property q3;\n"
          "      a |=> !b;\n"
          "    endproperty\n"
          "  endclocking\n"
          "  property q5;\n"
          "    @(negedge clk) a |=> !b;\n"
          "  endproperty\n"
          "  d1: assert property (q1) else $display(\"d1 at %0d\", $time);\n"
          "  d2: assert property (a |=> !b)\n"
          "    else $display(\"d2 at %0d\", $time);\n"
          "  d3: assert property (@(negedge clk) a |=> !b)\n"
          "    else $display(\"d3 at %0d\", $time);\n"
          "  d4: assert property (posedge_clk.q3)\n"
          "    else $display(\"d4 at %0d\", $time);\n"
          "  d5: assert property (q5) else $display(\"d5 at %0d\", $time);\n"
          "  always @(negedge clk) begin\n"
          "    p1: assert property (q1) else $display(\"p1 at %0d\", $time);\n"
          "    p2: assert property (posedge_clk.q3)\n"
          "      else $display(\"p2 at %0d\", $time);\n"
          "  end\n"
          "endmodule\n"),
      f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(out,
            "d1 at 25\nd2 at 25\nd4 at 25\np2 at 25\n"
            "d3 at 30\nd5 at 30\np1 at 30\n$finish at time 40\n");
}

// §16.16 (f): with no default clocking, an instance of a sequence or
// property declared with a clock takes that clock, the clause's c3 and its
// a4 in kind, beside a cover that writes its own.
TEST(ClockResolutionRun, WithoutADefaultAnInstanceDeterminesTheClock) {
  SimFixture f;
  std::string out = RunCapture(
      Design("module m(input logic a, b, clk);\n"
             "  property q5;\n"
             "    @(negedge clk) a |=> !b;\n"
             "  endproperty\n"
             "  sequence s2;\n"
             "    a ##1 b;\n"
             "  endsequence\n"
             "  sequence s3;\n"
             "    @(negedge clk) s2;\n"
             "  endsequence\n"
             "  e1: assert property (q5) else $display(\"e1 at %0d\", $time);\n"
             "  e2: cover property (@(negedge clk) s2)\n"
             "    $display(\"e2 at %0d\", $time);\n"
             "  e3: cover property (s3) $display(\"e3 at %0d\", $time);\n"
             "endmodule\n"),
      f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(out, "e1 at 30\ne2 at 30\ne3 at 30\n$finish at time 40\n");
}

}  // namespace
