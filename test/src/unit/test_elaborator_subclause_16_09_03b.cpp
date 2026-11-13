#include <gtest/gtest.h>

#include "helpers_marked_reports.h"

using namespace delta;

namespace {

constexpr const char* kLocalReport =
    "may not reference a local variable or the sequence method matched";

void ExpectLocalReports(const MarkedSource& marked) {
  ExpectMarkedReports(marked, kLocalReport, "16.9.3");
}

TEST(SampledArgumentLocals, ABodyLocalInEveryFunctionIsReported) {
  ExpectLocalReports(
      {"module sequences",
       "module m;\n"
       "  logic clk, a, b, en;\n"
       "  sequence s1; int v; @(posedge clk) (1, v = a) ##1 $sampled(v);"
       " endsequence\n"
       "  sequence s2; int v; @(posedge clk) (1, v = a) ##1 $rose(v);"
       " endsequence\n"
       "  sequence s3; int v; @(posedge clk) (1, v = a) ##1 $fell(v);"
       " endsequence\n"
       "  sequence s4; int v; @(posedge clk) (1, v = a) ##1 $changed(v);"
       " endsequence\n"
       "  sequence s5; int v; @(posedge clk) (1, v = a) ##1 $past(v) == 1;"
       " endsequence\n"
       "  sequence s6; @(posedge clk) a ##1 $sampled(b) ##1 $rose(b)"
       " ##1 $fell(b) ##1 $changed(b) ##1 $past(b) == 1; endsequence\n"
       "endmodule\n",
       {"sequence s1;", "sequence s2;", "sequence s3;", "sequence s4;",
        "sequence s5;"},
       {"sequence s6;"}});
}

TEST(SampledArgumentLocals, ALocalInAnyArgumentOrOperandIsReported) {
  ExpectLocalReports(
      {"module sequences",
       "module m;\n"
       "  logic clk, a, b, en;\n"
       "  sequence s1; int v; @(posedge clk) (1, v = a) ##1 $stable(v + 1);"
       " endsequence\n"
       "  sequence s2; int v; @(posedge clk) (1, v = a) ##1 $past(b, 1, v);"
       " endsequence\n"
       "  sequence s3; int v; @(posedge clk) (1, v = a) ##1 $past(b, v);"
       " endsequence\n"
       "  sequence s4; int v; @(posedge clk) (1, v = a) ##1 $past(b, 1, en)"
       " ##1 $stable(b + 1); endsequence\n"
       "endmodule\n",
       {"sequence s1;", "sequence s2;", "sequence s3;"},
       {"sequence s4;"}});
}

TEST(SampledArgumentLocals, ALocalFormalOrPropertyLocalIsReported) {
  ExpectLocalReports(
      {"module declarations",
       "module m;\n"
       "  logic clk, a, b;\n"
       "  sequence s1(local input int lv); @(posedge clk) a ##1 $past(lv) =="
       " 1; endsequence\n"
       "  sequence s2(lv); @(posedge clk) a ##1 $past(lv) == 1;"
       " endsequence\n"
       "  property p1(local input int lv); @(posedge clk) a |=> $past(lv) =="
       " 1; endproperty\n"
       "  property p2(lv); @(posedge clk) a |=> $past(lv) == 1;"
       " endproperty\n"
       "  property p3; int v; @(posedge clk) (a, v = b) |=> $fell(v);"
       " endproperty\n"
       "  property p4; int v; @(posedge clk) (a, v = b) |=> $past(v) == 1;"
       " endproperty\n"
       "  property p5; int v; @(posedge clk) (a, v = b) |=> $fell(b) &&"
       " v == 1; endproperty\n"
       "  a1: assert property (s2(a));\n"
       "  a2: assert property (p2(a));\n"
       "endmodule\n",
       {"sequence s1(", "property p1(", "property p3;", "property p4;"},
       {"sequence s2(", "property p2(", "property p5;", "a1:", "a2:"}});
}

TEST(SampledArgumentLocals, MatchedInAnyArgumentIsReported) {
  ExpectLocalReports(
      {"module assertions",
       "module m;\n"
       "  logic clk, a, b;\n"
       "  sequence t; @(posedge clk) a; endsequence\n"
       "  a1: assert property (@(posedge clk) $fell(t.matched));\n"
       "  a2: assert property (@(posedge clk) $stable(t.matched));\n"
       "  a3: assert property (@(posedge clk) $changed(t.matched));\n"
       "  a4: assert property (@(posedge clk) $sampled(t.matched));\n"
       "  a5: assert property (@(posedge clk) $past(t.matched));\n"
       "  a6: assert property (@(posedge clk) $past(b, 1, t.matched));\n"
       "  a7: assert property (@(posedge clk) $rose(t.matched && a));\n"
       "  a8: assert property (@(posedge clk)"
       " disable iff ($sampled(t.matched)) a);\n"
       "  sequence s4; @(posedge clk) a ##1 $fell(t.matched); endsequence\n"
       "  b1: assert property (@(posedge clk) $fell(t.triggered));\n"
       "  b2: assert property (@(posedge clk) $rose(b && a));\n"
       "  b3: assert property (@(posedge clk) disable iff ($sampled(b)) a);\n"
       "  sequence s5; @(posedge clk) a ##1 $fell(b) ##1 t.matched;"
       " endsequence\n"
       "endmodule\n",
       {"a1:", "a2:", "a3:", "a4:", "a5:", "a6:", "a7:", "a8:", "sequence s4;"},
       {"b1:", "b2:", "b3:", "sequence s5;"}});
}

TEST(SampledArgumentLocals, ALocalIsReportedInEveryDesignElement) {
  const MarkedSource kPlaces[] = {
      {"interface",
       "interface ifc(input logic clk, a);\n"
       "  sequence s1; int v; @(posedge clk) (1, v = a) ##1 $rose(v);"
       " endsequence\n"
       "  property p1; int v; @(posedge clk) (1, v = a) |=> $stable(v);"
       " endproperty\n"
       "  sequence s2; @(posedge clk) a ##1 $rose(a); endsequence\n"
       "endinterface\n"
       "module m;\n"
       "  logic clk, a;\n"
       "  ifc i(clk, a);\n"
       "endmodule\n",
       {"sequence s1;", "property p1;"},
       {"sequence s2;"}},
      {"program",
       "program pg(input logic clk, a);\n"
       "  sequence s1; int v; @(posedge clk) (1, v = a) ##1 $rose(v);"
       " endsequence\n"
       "  property p1; int v; @(posedge clk) (1, v = a) |=> $stable(v);"
       " endproperty\n"
       "  sequence s2; @(posedge clk) a ##1 $rose(a); endsequence\n"
       "endprogram\n"
       "module m;\n"
       "  logic clk, a;\n"
       "  pg p(clk, a);\n"
       "endmodule\n",
       {"sequence s1;", "property p1;"},
       {"sequence s2;"}},
      {"checker",
       "checker ck(logic clk, logic a);\n"
       "  sequence s1; int v; @(posedge clk) (1, v = a) ##1 $rose(v);"
       " endsequence\n"
       "  property p1; int v; @(posedge clk) (1, v = a) |=> $stable(v);"
       " endproperty\n"
       "  sequence s2; @(posedge clk) a ##1 $rose(a); endsequence\n"
       "endchecker\n"
       "module m;\n"
       "  logic clk, a;\n"
       "  ck k(clk, a);\n"
       "endmodule\n",
       {"sequence s1;", "property p1;"},
       {"sequence s2;"}}};
  for (const MarkedSource& place : kPlaces) ExpectLocalReports(place);
}

TEST(SampledArgumentLocals, DISABLED_ALocalIsReportedOutsideADesignElement) {
  const MarkedSource kPlaces[] = {
      {"package",
       "package pk;\n"
       "  sequence ps; int v; (1, v = 1'b1) ##1 $rose(v); endsequence\n"
       "  property pp; int v; (1, v = 1'b1) |=> $stable(v); endproperty\n"
       "  sequence pq(x); x ##1 $rose(x); endsequence\n"
       "endpackage\n"
       "module m;\n"
       "  logic clk, a;\n"
       "  a1: assert property (@(posedge clk) pk::ps);\n"
       "  a2: assert property (@(posedge clk) pk::pp);\n"
       "  a3: assert property (@(posedge clk) pk::pq(a));\n"
       "endmodule\n",
       {"sequence ps;", "property pp;"},
       {"sequence pq(", "a3:"}},
      {"compilation unit",
       "sequence us; int v; (1, v = 1'b1) ##1 $rose(v); endsequence\n"
       "property up; int v; (1, v = 1'b1) |=> $stable(v); endproperty\n"
       "sequence uq(x); x ##1 $rose(x); endsequence\n"
       "module m;\n"
       "  logic clk, a;\n"
       "  a1: assert property (@(posedge clk) us);\n"
       "  a2: assert property (@(posedge clk) up);\n"
       "  a3: assert property (@(posedge clk) uq(a));\n"
       "endmodule\n",
       {"sequence us;", "property up;"},
       {"sequence uq(", "a3:"}},
      {"generate block",
       "module m;\n"
       "  logic clk, a;\n"
       "  if (1) begin : g\n"
       "    sequence gs; int v; @(posedge clk) (1, v = a) ##1 $fell(v);"
       " endsequence\n"
       "    property gp; int v; @(posedge clk) (1, v = a) |=> $stable(v);"
       " endproperty\n"
       "    sequence gq; @(posedge clk) a ##1 $fell(a); endsequence\n"
       "    a4: assert property (gs);\n"
       "  end\n"
       "endmodule\n",
       {"sequence gs;", "property gp;"},
       {"sequence gq;"}}};
  for (const MarkedSource& place : kPlaces) ExpectLocalReports(place);
}

}  // namespace
