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

// §16.16 (f) with §9.4 Syntax 9-4: a sequence whose leading clocking event is
// written as a bare name, `@clk`, is declared with that event, which an
// instance with no default clocking takes: every edge of clk, so a is sampled
// 1 at 20 and b 1 at 25, and a ##1 b matches once, at 25.
TEST(ClockResolutionRun, ASequenceClockedByABareNameTakesThatClock) {
  SimFixture f;
  std::string out = RunCapture(
      Design("module m(input logic a, b, clk);\n"
             "  sequence s4;\n"
             "    @clk a ##1 b;\n"
             "  endsequence\n"
             "  e4: cover property (s4) $display(\"e4 at %0d\", $time);\n"
             "endmodule\n"),
      f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(out, "e4 at 25\n$finish at time 40\n");
}

// §9.4 Syntax 9-4: the clocking event of an assertion written as a bare
// name ends at the name, so `@clk (a) ##1 b` is clocked by every edge of clk
// and opens with the operand (a), rather than waiting on a call `clk(a)`.
TEST(ClockResolutionRun, AnAssertionsBareNamedClockEndsAtTheName) {
  SimFixture f;
  std::string out = RunCapture(Design("module m(input logic a, b, clk);\n"
                                      "  e5: cover property (@clk (a) ##1 b)\n"
                                      "    $display(\"e5 at %0d\", $time);\n"
                                      "endmodule\n"),
                               f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(out, "e5 at 25\n$finish at time 40\n");
}

// The same for a named property declared with a bare named clock.
TEST(ClockResolutionRun, APropertysBareNamedClockEndsAtTheName) {
  SimFixture f;
  std::string out = RunCapture(
      Design("module m(input logic a, b, clk);\n"
             "  property q6;\n"
             "    @clk (a) ##1 b;\n"
             "  endproperty\n"
             "  e6: cover property (q6) $display(\"e6 at %0d\", $time);\n"
             "endmodule\n"),
      f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(out, "e6 at 25\n$finish at time 40\n");
}

// §16.16 (f) with §16.12: a property declared in an interface with its own
// clocking event is instantiated by the hierarchical name of an interface
// instance, `i0.low`, and takes that event as the assertion's clock; its
// body reads the instance's own clock and signal, so i0 and i1, bound to
// different patterns, fail at different ticks: i0 where av holds 0, three
// times, and i1 where bv does, five.
TEST(ClockResolutionRun, AnInterfacePropertyInstancedByPathTakesItsClock) {
  SimFixture f;
  std::string out = RunCapture(
      "interface ifc(input logic clk);\n"
      "  logic sig;\n"
      "  property low; @(posedge clk) !sig; endproperty\n"
      "endinterface\n"
      "module t;\n"
      "  logic clk = 0;\n"
      "  initial repeat (20) #5 clk = ~clk;\n"
      "  bit [0:9] av = 10'b1101001111, bv = 10'b0000011111;\n"
      "  always @(negedge clk) begin av <= av << 1; bv <= bv << 1; end\n"
      "  ifc i0(clk), i1(clk);\n"
      "  assign i0.sig = !av[0];\n"
      "  assign i1.sig = !bv[0];\n"
      "  int f0 = 0, f1 = 0;\n"
      "  assert property (i0.low) else f0++;\n"
      "  assert property (i1.low) else f1++;\n"
      "  initial #98 $display(\"f0=%0d f1=%0d\", f0, f1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(out, "f0=3 f1=5\n");
}

// §16.16 (f) with §16.12 and §23.6: the same for a property whose body is
// temporal, `a |=> b`, which reads the instance's own clock and signals. At
// clk's rises i0's a is 1101001111 and its b 0110011110, so the implication
// fails from the ticks 3 and 8, twice; i1 has the two patterns swapped and
// fails from the tick 1 alone.
TEST(ClockResolutionRun, AnInterfacePropertyWithATemporalBodyTakesItsClock) {
  SimFixture f;
  std::string out = RunCapture(
      "interface ifc(input logic clk);\n"
      "  logic a, b;\n"
      "  property p; @(posedge clk) a |=> b; endproperty\n"
      "endinterface\n"
      "module t;\n"
      "  logic clk = 0;\n"
      "  initial repeat (20) #5 clk = ~clk;\n"
      "  bit [0:9] av = 10'b1101001111, bv = 10'b0110011110;\n"
      "  always @(negedge clk) begin av <= av << 1; bv <= bv << 1; end\n"
      "  ifc i0(clk), i1(clk);\n"
      "  assign i0.a = av[0]; assign i0.b = bv[0];\n"
      "  assign i1.a = bv[0]; assign i1.b = av[0];\n"
      "  int f0 = 0, f1 = 0;\n"
      "  assert property (i0.p) else f0++;\n"
      "  assert property (i1.p) else f1++;\n"
      "  initial #98 $display(\"f0=%0d f1=%0d\", f0, f1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(out, "f0=2 f1=1\n");
}

// The property's read of a member of the interface's struct, `pair.lo`, is
// rewritten through the instance like a whole signal: each instance's
// assertion reads its own `pair`, and the two fail on different cycles.
TEST(ClockResolutionRun, AnInterfacePropertyReadsTheInstancesStructMember) {
  SimFixture f;
  std::string out = RunCapture(
      "interface ifc(input logic clk);\n"
      "  struct packed { logic hi; logic lo; } pair;\n"
      "  property low; @(posedge clk) !pair.lo; endproperty\n"
      "endinterface\n"
      "module t;\n"
      "  logic clk = 0;\n"
      "  initial repeat (20) #5 clk = ~clk;\n"
      "  bit [0:9] av = 10'b1101001111, bv = 10'b0000011111;\n"
      "  always @(negedge clk) begin av <= av << 1; bv <= bv << 1; end\n"
      "  ifc i0(clk), i1(clk);\n"
      "  assign i0.pair = {av[0], !av[0]};\n"
      "  assign i1.pair = {bv[0], !bv[0]};\n"
      "  int f0 = 0, f1 = 0;\n"
      "  assert property (i0.low) else f0++;\n"
      "  assert property (i1.low) else f1++;\n"
      "  initial #98 $display(\"f0=%0d f1=%0d\", f0, f1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(out, "f0=3 f1=5\n");
}

}  // namespace
