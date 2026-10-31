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

// §16.12 with §23.6: a property declared in an interface and instantiated by
// the path of an instance reads the instance's own signals whatever the shape
// of its body: a local variable assigned in a match item, a clock named again
// before an operand of a sequence or of a property, an or, an and and an
// intersect of properties, a first_match with a match item and one over an or
// and over an and of sequences, a case and a throughout. Each is asserted
// beside the same property declared in the module over the module's signals,
// which the instance's are bound to, and fails as often.
TEST(ClockResolutionRun, AnInterfacePropertyOfEachBodyShapeReadsTheInstance) {
  SimFixture f;
  std::string out = RunCapture(
      "interface ifc(input logic clk);\n"
      "  logic a, b, c, d, sel;\n"
      "  property p_local; bit v; @(posedge clk) (a, v = b) |=> (c == v); "
      "endproperty\n"
      "  property p_clk; @(posedge clk) a ##1 @(posedge clk) b; endproperty\n"
      "  property p_or; @(posedge clk) (a ##1 b) or (c ##2 d); endproperty\n"
      "  property p_and; @(posedge clk) (a ##1 b) and (c ##1 d); endproperty\n"
      "  property p_int; @(posedge clk) (a ##[1:2] b) intersect (c ##2 d); "
      "endproperty\n"
      "  property p_node; @(posedge clk) a |=> @(posedge clk) b; endproperty\n"
      "  property p_fm; bit v; @(posedge clk) first_match(a ##[1:2] b, v = c) "
      "|=> (d == v); endproperty\n"
      "  property p_fo; @(posedge clk) first_match((a ##1 b) or (c ##1 d)) |=> "
      "a; endproperty\n"
      "  property p_fa; @(posedge clk) first_match((a ##1 b) and (c ##1 d)) "
      "|=> b; endproperty\n"
      "  property p_case; @(posedge clk) case (sel) 1'b0: a; default: b; "
      "endcase; endproperty\n"
      "  property p_thr; @(posedge clk) a throughout (b ##1 c); endproperty\n"
      "endinterface\n"
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  bit [0:9] av = 10'b1101001111, bv = 10'b0110011110, cv = "
      "10'b1011010011, dv = 10'b0111100101, sv = 10'b0011001100;\n"
      "  always @(negedge clk) begin av <= av << 1; bv <= bv << 1; cv <= cv << "
      "1; dv <= dv << 1; sv <= sv << 1; end\n"
      "  logic a, b, c, d, sel;\n"
      "  assign a = av[0]; assign b = bv[0]; assign c = cv[0]; assign d = "
      "dv[0]; assign sel = sv[0];\n"
      "  ifc i0(clk);\n"
      "  assign i0.a = a; assign i0.b = b; assign i0.c = c; assign i0.d = d; "
      "assign i0.sel = sel;\n"
      "  property m_local; bit v; @(posedge clk) (a, v = b) |=> (c == v); "
      "endproperty\n"
      "  property m_clk; @(posedge clk) a ##1 @(posedge clk) b; endproperty\n"
      "  property m_or; @(posedge clk) (a ##1 b) or (c ##2 d); endproperty\n"
      "  property m_and; @(posedge clk) (a ##1 b) and (c ##1 d); endproperty\n"
      "  property m_int; @(posedge clk) (a ##[1:2] b) intersect (c ##2 d); "
      "endproperty\n"
      "  property m_node; @(posedge clk) a |=> @(posedge clk) b; endproperty\n"
      "  property m_fm; bit v; @(posedge clk) first_match(a ##[1:2] b, v = c) "
      "|=> (d == v); endproperty\n"
      "  property m_fo; @(posedge clk) first_match((a ##1 b) or (c ##1 d)) |=> "
      "a; endproperty\n"
      "  property m_fa; @(posedge clk) first_match((a ##1 b) and (c ##1 d)) "
      "|=> b; endproperty\n"
      "  property m_case; @(posedge clk) case (sel) 1'b0: a; default: b; "
      "endcase; endproperty\n"
      "  property m_thr; @(posedge clk) a throughout (b ##1 c); endproperty\n"
      "  int fi[11], fm[11];\n"
      "  assert property (i0.p_local) else fi[0]++;   assert property "
      "(m_local) else fm[0]++;\n"
      "  assert property (i0.p_clk) else fi[1]++;     assert property (m_clk) "
      "else fm[1]++;\n"
      "  assert property (i0.p_or) else fi[2]++;      assert property (m_or) "
      "else fm[2]++;\n"
      "  assert property (i0.p_and) else fi[3]++;     assert property (m_and) "
      "else fm[3]++;\n"
      "  assert property (i0.p_int) else fi[4]++;     assert property (m_int) "
      "else fm[4]++;\n"
      "  assert property (i0.p_case) else fi[5]++;    assert property (m_case) "
      "else fm[5]++;\n"
      "  assert property (i0.p_thr) else fi[6]++;     assert property (m_thr) "
      "else fm[6]++;\n"
      "  assert property (i0.p_node) else fi[7]++;    assert property (m_node) "
      "else fm[7]++;\n"
      "  assert property (i0.p_fm) else fi[8]++;      assert property (m_fm) "
      "else fm[8]++;\n"
      "  assert property (i0.p_fo) else fi[9]++;     assert property (m_fo) "
      "else fm[9]++;\n"
      "  assert property (i0.p_fa) else fi[10]++;    assert property (m_fa) "
      "else fm[10]++;\n"
      "  initial #98 for (int i = 0; i < 11; i++) $display(\"%0d: ifc=%0d "
      "mod=%0d\", i, fi[i], fm[i]);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_EQ(out,
            "0: ifc=1 mod=1\n1: ifc=5 mod=5\n2: ifc=2 mod=2\n"
            "3: ifc=8 mod=8\n4: ifc=7 mod=7\n5: ifc=3 mod=3\n"
            "6: ifc=8 mod=8\n7: ifc=2 mod=2\n8: ifc=2 mod=2\n"
            "9: ifc=3 mod=3\n10: ifc=0 mod=0\n");
}

// §16.16 (d) with §F.4.1: an instance whose body is a formal given an actual
// that opens with its clocking event runs on that event. clk rises at 5, 15,
// 25 and 35 before the run ends at 42, so each assertion on posedge clk
// passes four times, the one on `@clk`, either edge, eight times, and the
// one in an initial procedure, attempted once, once; so does the instance
// given pc(a), an instance of a property declared on posedge clk, four
// times. Each assertion had been reported as unclocked.
TEST(ClockedActualRun, AClockedActualClocksTheInstance) {
  SimFixture f;
  std::string out = RunCapture(
      "module m;\n"
      "  logic clk = 0, a = 1;\n"
      "  int ns, np, nu, nq, ne, ni, nc;\n"
      "  always #5 clk = ~clk;\n"
      "  property ps(sequence s); s; endproperty\n"
      "  property pp(property p); p; endproperty\n"
      "  property pu(u); u; endproperty\n"
      "  sequence qs(sequence s); s; endsequence\n"
      "  property pc(x); @(posedge clk) x; endproperty\n"
      "  assert property (ps(@(posedge clk) a)) ns++;\n"
      "  assert property (pp(@(posedge clk) a |-> a)) np++;\n"
      "  assert property (pu(@(posedge clk) a)) nu++;\n"
      "  cover property (qs(@(posedge clk) a)) nq++;\n"
      "  assert property (ps(@clk a)) ne++;\n"
      "  initial assert property (qs(@(posedge clk) a)) ni++;\n"
      "  assert property (pp(pc(a))) nc++;\n"
      "  initial #42 begin\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d %0d\", ns, np, nu, nq, ne, ni,\n"
      "             nc);\n"
      "    $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("4 4 4 4 8 1 4\n"), std::string::npos) << out;
}

// §16.16 (d) with §17.3 and §14.14: a checker asserting, assuming and
// covering its formals runs on the clock of each actual its instance gives:
// c1's on posedge fast, rising four times by 42, and c2's on
// `@($global_clock)` and `@$global_clock`, which resolve in the checker to
// its own global clocking on posedge slow, rising twice.
TEST(ClockedActualRun, ACheckerFormalRunsOnItsActualsClock) {
  SimFixture f;
  std::string out = RunCapture(
      "checker chk(property p, sequence s, logic cclk);\n"
      "  int na, nm, nc;\n"
      "  global clocking @(posedge cclk); endclocking\n"
      "  assert property (p) na++;\n"
      "  assume property (p) nm++;\n"
      "  cover property (s) nc++;\n"
      "endchecker\n"
      "module m;\n"
      "  logic fast = 0, slow = 0, a = 1;\n"
      "  always #5 fast = ~fast;\n"
      "  always #10 slow = ~slow;\n"
      "  global clocking @(posedge fast); endclocking\n"
      "  chk c1(@(posedge fast) a, @(posedge fast) a, slow);\n"
      "  chk c2(@($global_clock) a, @$global_clock a, slow);\n"
      "  initial #42 begin\n"
      "    $display(\"%0d %0d %0d\", c1.na, c1.nm, c1.nc);\n"
      "    $display(\"%0d %0d %0d\", c2.na, c2.nm, c2.nc);\n"
      "    $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("4 4 4\n2 2 2\n"), std::string::npos) << out;
}

// §16.16 (f) with §16.16.1: each instance below runs on negedge clk, the one
// clock its body determines through s2. a and b follow clk, so each samples 1
// at a negedge, at 10, 20, 30 and 40 before the run ends at 42, and 0 at a
// posedge: s2, a ##1 b, matches from 10, 20 and 30, and would match from
// none on posedge clk. So `not s2` and `not pg` fail three times; `s2 and
// s2`, `s2 or s2`, the aborts, pg's instance, `s2 ##0 b`, `(s2)`, `s2 |-> a`
// and s2 alone pass or match three times; and `s2 ##1 b` and `s2 |=> a`,
// one tick longer, twice. Each instance had been reported as unclocked.
TEST(DeterminedClockRun, ABodyRunsOnTheClockItDetermines) {
  SimFixture f;
  std::string out = RunCapture(
      "module m;\n"
      "  logic clk = 0;\n"
      "  wire a = clk, b = clk;\n"
      "  int n[13];\n"
      "  always #5 clk = ~clk;\n"
      "  sequence s2; @(negedge clk) a ##1 b; endsequence\n"
      "  property p2; not s2; endproperty\n"
      "  property pe; s2 and s2; endproperty\n"
      "  property po; s2 or s2; endproperty\n"
      "  property pa; accept_on(1'b0) s2; endproperty\n"
      "  property pr; reject_on(1'b0) s2; endproperty\n"
      "  property pg; s2; endproperty\n"
      "  property pi; pg; endproperty\n"
      "  property pn; not pg; endproperty\n"
      "  sequence sk; s2 ##1 b; endsequence\n"
      "  sequence sz; s2 ##0 b; endsequence\n"
      "  sequence sp; (s2); endsequence\n"
      "  property pm; s2 |-> a; endproperty\n"
      "  property pd; s2 |=> a; endproperty\n"
      "  assert property (p2) else n[0]++;\n"
      "  assert property (pe) n[1]++;\n"
      "  assert property (po) n[2]++;\n"
      "  assert property (pa) n[3]++;\n"
      "  assert property (pr) n[4]++;\n"
      "  assert property (pi) n[5]++;\n"
      "  assert property (pn) else n[6]++;\n"
      "  cover property (sk) n[7]++;\n"
      "  cover property (sz) n[8]++;\n"
      "  cover property (sp) n[9]++;\n"
      "  assert property (pm) n[10]++;\n"
      "  assert property (pd) n[11]++;\n"
      "  assert property (s2) n[12]++;\n"
      "  initial #42 begin\n"
      "    foreach (n[i]) $write(\"%0d \", n[i]);\n"
      "    $display;\n"
      "    $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("3 3 3 3 3 3 3 2 3 3 3 2 3 \n"), std::string::npos) << out;
}

// §16.16 (f) with §23.9, §3.12.1 and §26.3: an instance runs on the clock of
// the declaration its place reaches: one a generate if block or a generate
// for block declares, on negedge clk, at 10, 20, 30 and 40; the compilation
// unit's, given posedge clk, at 5, 15, 25 and 35; and a package's, named
// `pk::pr(a, clk)` and `pk::pq`, likewise four times. a and b are 1 at every
// tick, so each passes four times.
TEST(DeterminedClockRun, AnInstanceRunsOnTheClockItsScopeDeclares) {
  SimFixture f;
  std::string out = RunCapture(
      "property cuq(x, c); @(posedge c) x; endproperty\n"
      "package pk;\n"
      "  bit pk_clk;\n"
      "  property pq; @(posedge pk_clk) 1; endproperty\n"
      "  property pr(x, c); @(posedge c) x; endproperty\n"
      "endpackage\n"
      "module m;\n"
      "  logic clk = 0, a = 1;\n"
      "  int ni, nf, nc, np, nq;\n"
      "  always #5 clk = ~clk;\n"
      "  always #5 pk::pk_clk = ~pk::pk_clk;\n"
      "  if (1) begin : gi\n"
      "    property pgi; @(negedge clk) a; endproperty\n"
      "    assert property (pgi) ni++;\n"
      "  end\n"
      "  for (genvar k = 0; k < 1; k++) begin : gf\n"
      "    sequence sgf; @(negedge clk) a; endsequence\n"
      "    cover property (sgf) nf++;\n"
      "  end\n"
      "  assert property (cuq(a, clk)) nc++;\n"
      "  assert property (pk::pr(a, clk)) np++;\n"
      "  assert property (pk::pq) nq++;\n"
      "  initial #42 begin\n"
      "    $display(\"%0d %0d %0d %0d %0d\", ni, nf, nc, np, nq);\n"
      "    $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("4 4 4 4 4\n"), std::string::npos) << out;
}

}  // namespace
