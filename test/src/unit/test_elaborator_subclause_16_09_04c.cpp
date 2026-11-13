#include <gtest/gtest.h>

#include <string>

#include "helpers_marked_reports.h"

using namespace delta;

namespace {

constexpr const char* kMatchReport =
    "a global clocking future sampled value function may not stand in an "
    "assertion that holds a sequence match item";

void ExpectMatchReports(const MarkedSource& marked) {
  ExpectMarkedReports(marked, kMatchReport, "16.9.4");
}

std::string GlobalModule(const std::string& items) {
  return "module m;\n"
         "  bit clk, a, b, c;\n"
         "  global clocking @(posedge clk); endclocking\n"
         "  sequence s1; bit v; (a, v = a) ##1 (b == v); endsequence\n"
         "  sequence t1; a ##1 b; endsequence\n" +
         items + "endmodule\n";
}

TEST(FutureGclkMatchItems, AMatchItemInlineOrInASequenceIsReported) {
  ExpectMatchReports(
      {"match items inline and in sequences",
       GlobalModule(
           "  sequence s6; s1 ##1 b; endsequence\n"
           "  sequence t6; t1 ##1 b; endsequence\n"
           "  sequence s4(sequence x); x ##1 b; endsequence\n"
           "  a1: assert property (@(posedge clk) (a, $display(\"m\")) |=>"
           " $falling_gclk(c));\n"
           "  a2: assert property (@(posedge clk) s6 |=> $future_gclk(c));\n"
           "  a3: assert property (@(posedge clk) s4(s1) |=> "
           "$future_gclk(c));\n"
           "  b1: assert property (@(posedge clk) a |=> $falling_gclk(c));\n"
           "  b2: assert property (@(posedge clk) t6 |=> $future_gclk(c));\n"
           "  b3: assert property (@(posedge clk) s4(t1) |=> "
           "$future_gclk(c));\n"
           "  b4: assert property (@(posedge clk) s4(a) |=> "
           "$future_gclk(c));\n"),
       {"a1:", "a2:", "a3:"},
       {"b1:", "b2:", "b3:", "b4:"}});
}

TEST(FutureGclkMatchItems, DISABLED_AMatchItemOrFunctionInAPropertyIsReported) {
  ExpectMatchReports(
      {"named properties",
       GlobalModule(
           "  property p1; bit v; (a, v = b) |=> $rising_gclk(c); endproperty\n"
           "  property p2; bit v; (a, v = b) |=> c; endproperty\n"
           "  property p3; a |=> $changing_gclk(c); endproperty\n"
           "  property k7; int v; (a, v = 0, v += 2) |=> b; endproperty\n"
           "  property p7; p2 and $rising_gclk(c); endproperty\n"
           "  property q1; a |=> $rising_gclk(c); endproperty\n"
           "  property q2; a |=> c; endproperty\n"
           "  property q7; q2 and $rising_gclk(c); endproperty\n"
           "  a1: assert property (@(posedge clk) p1);\n"
           "  a2: assert property (@(posedge clk) p2 and $steady_gclk(c));\n"
           "  a3: assert property (@(posedge clk) s1 |=> p3);\n"
           "  a4: assert property (@(posedge clk) (a, $display(\"m\")) |=> "
           "p3);\n"
           "  a5: assert property (@(posedge clk) k7 and $future_gclk(c));\n"
           "  a6: assert property (@(posedge clk) p7);\n"
           "  b1: assert property (@(posedge clk) q1);\n"
           "  b2: assert property (@(posedge clk) q2 and $steady_gclk(c));\n"
           "  b3: assert property (@(posedge clk) t1 |=> p3);\n"
           "  b6: assert property (@(posedge clk) q7);\n"),
       {"a1:", "a2:", "a3:", "a4:", "a5:", "a6:"},
       {"b1:", "b2:", "b3:", "b6:"}});
}

TEST(FutureGclkMatchItems,
     DISABLED_AFunctionInASequenceOrAnInlineActualIsReported) {
  ExpectMatchReports(
      {"sequences and inline actuals",
       GlobalModule(
           "  sequence s5; $future_gclk(c); endsequence\n"
           "  sequence s4(sequence x); x ##1 b; endsequence\n"
           "  a1: assert property (@(posedge clk) s1 ##1 s5);\n"
           "  a2: assert property (@(posedge clk) s4((a, $display(\"m\"))) |=>"
           " $future_gclk(c));\n"
           "  b1: assert property (@(posedge clk) t1 ##1 s5);\n"
           "  b2: assert property (@(posedge clk) s4((a)) |=> "
           "$future_gclk(c));\n"),
       {"a1:", "a2:"},
       {"b1:", "b2:"}});
}

TEST(FutureGclkMatchItems, EveryKindOfMatchItemIsReported) {
  ExpectMatchReports(
      {"kinds of match item",
       GlobalModule(
           "  task automatic tk(); endtask\n"
           "  function automatic void vf(); endfunction\n"
           "  sequence k1; int v; (a, v = 0, v++) ##1 b; endsequence\n"
           "  sequence k2; int v; (a, v = 0, v--) ##1 b; endsequence\n"
           "  sequence k3; int v; (a, v = 0, v += 1) ##1 b; endsequence\n"
           "  sequence k4; (a, $display(\"m\")) ##1 b; endsequence\n"
           "  sequence k5; (a, tk()) ##1 b; endsequence\n"
           "  sequence k6; (a, vf()) ##1 b; endsequence\n"
           "  a1: assert property (@(posedge clk) k1 |=> $future_gclk(c));\n"
           "  a2: assert property (@(posedge clk) k2 |=> $future_gclk(c));\n"
           "  a3: assert property (@(posedge clk) k3 |=> $future_gclk(c));\n"
           "  a4: assert property (@(posedge clk) k4 |=> $future_gclk(c));\n"
           "  a5: assert property (@(posedge clk) k5 |=> $future_gclk(c));\n"
           "  a6: assert property (@(posedge clk) k6 |=> $future_gclk(c));\n"
           "  a8: assert property (@(posedge clk) (a, tk()) |=>"
           " $future_gclk(c));\n"
           "  a9: assert property (@(posedge clk) (a, vf()) |=>"
           " $future_gclk(c));\n"
           "  b1: assert property (@(posedge clk) a ##1 b |=> "
           "$future_gclk(c));\n"),
       {"a1:", "a2:", "a3:", "a4:", "a5:", "a6:", "a8:", "a9:"},
       {"b1:"}});
}

TEST(FutureGclkMatchItems, EveryFutureFunctionIsReportedAndNoPastOne) {
  ExpectMatchReports(
      {"future and past functions",
       GlobalModule(
           "  a1: assert property (@(posedge clk) s1 |=> $future_gclk(c));\n"
           "  a2: assert property (@(posedge clk) s1 |=> $rising_gclk(c));\n"
           "  a3: assert property (@(posedge clk) s1 |=> $falling_gclk(c));\n"
           "  a4: assert property (@(posedge clk) s1 |=> $steady_gclk(c));\n"
           "  a5: assert property (@(posedge clk) s1 |=> $changing_gclk(c));\n"
           "  b1: assert property (@(posedge clk) s1 |=> $past_gclk(c));\n"
           "  b2: assert property (@(posedge clk) s1 |=> $rose_gclk(c));\n"
           "  b3: assert property (@(posedge clk) s1 |=> $fell_gclk(c));\n"
           "  b4: assert property (@(posedge clk) s1 |=> $stable_gclk(c));\n"
           "  b5: assert property (@(posedge clk) s1 |=> $changed_gclk(c));\n"),
       {"a1:", "a2:", "a3:", "a4:", "a5:"},
       {"b1:", "b2:", "b3:", "b4:", "b5:"}});
}

TEST(FutureGclkMatchItems, EveryPropertyStatementIsHeldToTheRule) {
  ExpectMatchReports(
      {"property statements",
       GlobalModule(
           "  a1: assume property (@(posedge clk) s1 |=> $rising_gclk(c));\n"
           "  a2: cover property (@(posedge clk) s1 |=> $rising_gclk(c));\n"
           "  a3: restrict property (@(posedge clk) s1 |=> $rising_gclk(c));\n"
           "  always @(posedge clk) begin\n"
           "    a6: assert property (s1 |=> $rising_gclk(c));\n"
           "    b6: assert property (t1 |=> $rising_gclk(c));\n"
           "  end\n"
           "  b1: assume property (@(posedge clk) t1 |=> $rising_gclk(c));\n"
           "  b2: cover property (@(posedge clk) t1 |=> $rising_gclk(c));\n"
           "  b3: restrict property (@(posedge clk) t1 |=> "
           "$rising_gclk(c));\n"),
       {"a1:", "a2:", "a3:", "a6:"},
       {"b1:", "b2:", "b3:", "b6:"}});
}

TEST(FutureGclkMatchItems, DISABLED_ACoverSequenceIsHeldToTheRule) {
  ExpectMatchReports(
      {"cover sequence",
       GlobalModule(
           "  a1: cover sequence (@(posedge clk) (a, $display(\"m\")) ##1"
           " $rising_gclk(c));\n"
           "  a2: cover sequence (@(posedge clk) s1 ##1 $rising_gclk(c));\n"
           "  b1: cover sequence (@(posedge clk) a ##1 $rising_gclk(c));\n"
           "  b2: cover sequence (@(posedge clk) t1 ##1 $rising_gclk(c));\n"),
       {"a1:", "a2:"},
       {"b1:", "b2:"}});
}

TEST(FutureGclkMatchItems, AnAssertionInEveryDesignElementIsHeldToTheRule) {
  ExpectMatchReports(
      {"interface, program and checker",
       "interface ifc(input logic clk, a, c);\n"
       "  a1: assert property (@(posedge clk) (a, $display(\"m\")) |=>"
       " $steady_gclk(c));\n"
       "  b1: assert property (@(posedge clk) a |=> $steady_gclk(c));\n"
       "endinterface\n"
       "program pg(input logic clk, a, c);\n"
       "  a2: assert property (@(posedge clk) (a, $display(\"m\")) |=>"
       " $steady_gclk(c));\n"
       "  b2: assert property (@(posedge clk) a |=> $steady_gclk(c));\n"
       "endprogram\n"
       "checker ck(bit clk, bit a, bit c);\n"
       "  a3: assert property (@(posedge clk) (a, $display(\"m\")) |=>"
       " $steady_gclk(c));\n"
       "  b3: assert property (@(posedge clk) a |=> $steady_gclk(c));\n"
       "endchecker\n"
       "module m;\n"
       "  bit clk, a, c;\n"
       "  global clocking @(posedge clk); endclocking\n"
       "  ifc i(clk, a, c);\n"
       "  pg p(clk, a, c);\n"
       "  ck k(clk, a, c);\n"
       "endmodule\n",
       {"a1:", "a2:", "a3:"},
       {"b1:", "b2:", "b3:"}});
}

TEST(FutureGclkMatchItems,
     DISABLED_AnAssertionInAGenerateBlockIsHeldToTheRule) {
  ExpectMatchReports(
      {"generate blocks",
       GlobalModule(
           "  if (1) begin : h\n"
           "    sequence gs; bit v; (a, v = a) ##1 b; endsequence\n"
           "    sequence gt; a ##1 b; endsequence\n"
           "    a1: assert property (@(posedge clk) (a, $display(\"m\")) |=>"
           " $future_gclk(c));\n"
           "    a2: assert property (@(posedge clk) gs |=> $future_gclk(c));\n"
           "    b1: assert property (@(posedge clk) a |=> $future_gclk(c));\n"
           "    b2: assert property (@(posedge clk) gt |=> $future_gclk(c));\n"
           "  end\n"
           "  for (genvar i = 0; i < 1; i++) begin : g\n"
           "    a3: assert property (@(posedge clk) s1 |=> $future_gclk(c));\n"
           "    b3: assert property (@(posedge clk) t1 |=> $future_gclk(c));\n"
           "  end\n"),
       {"a1:", "a2:", "a3:"},
       {"b1:", "b2:", "b3:"}});
}

TEST(FutureGclkMatchItems,
     DISABLED_ASequenceOutsideADesignElementIsHeldToTheRule) {
  ExpectMatchReports(
      {"package and compilation unit",
       "package pk;\n"
       "  sequence ps; bit v; (1, v = 1'b1) ##1 v; endsequence\n"
       "  property pp; bit v; (1, v = 1'b1) |=> v; endproperty\n"
       "  sequence pt; 1 ##1 1; endsequence\n"
       "endpackage\n"
       "sequence us; bit v; (1, v = 1'b1) ##1 v; endsequence\n"
       "sequence ut; 1 ##1 1; endsequence\n"
       "module m;\n"
       "  bit clk, c;\n"
       "  global clocking @(posedge clk); endclocking\n"
       "  a1: assert property (@(posedge clk) pk::ps |=> $future_gclk(c));\n"
       "  a2: assert property (@(posedge clk) pk::pp and $future_gclk(c));\n"
       "  a3: assert property (@(posedge clk) us |=> $future_gclk(c));\n"
       "  b1: assert property (@(posedge clk) pk::pt |=> $future_gclk(c));\n"
       "  b3: assert property (@(posedge clk) ut |=> $future_gclk(c));\n"
       "endmodule\n",
       {"a1:", "a2:", "a3:"},
       {"b1:", "b3:"}});
}

}  // namespace
