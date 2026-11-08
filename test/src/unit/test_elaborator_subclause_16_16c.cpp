#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

const char* const kNoClockReport =
    "concurrent assertion has no leading clocking event";

TEST(ClockedActualElaboration, AClockedActualGivesTheInstanceItsClock) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic clk, a;\n"
      "  property ps(sequence s); s; endproperty\n"
      "  property pp(property p); p; endproperty\n"
      "  property pu(u); u; endproperty\n"
      "  sequence qs(sequence s); s; endsequence\n"
      "  property pc(x); @(posedge clk) x; endproperty\n"
      "  assert property (ps(@(posedge clk) a));\n"
      "  assert property (pp(@(posedge clk) a |-> a));\n"
      "  assert property (pp(pc(a)));\n"
      "  assert property (pu(@(posedge clk) a));\n"
      "  cover property (qs(@(posedge clk) a));\n"
      "  assert property (ps(@clk a));\n"
      "  initial assert property (ps(@(posedge clk) a));\n"
      "  always @(a) assert property (qs(@(posedge clk) a));\n"
      "endmodule\n"
      "interface i;\n"
      "  logic clk, a;\n"
      "  property ps(sequence s); s; endproperty\n"
      "  assert property (ps(@(posedge clk) a));\n"
      "endinterface\n"
      "program g;\n"
      "  logic clk, a;\n"
      "  property ps(sequence s); s; endproperty\n"
      "  assert property (ps(@(posedge clk) a));\n"
      "endprogram\n",
      f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
}

TEST(ClockedActualElaboration, AnUnclockedOrTwiceClockedActualIsReported) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic clk, c2, a;\n"
      "  property ps(sequence s); s; endproperty\n"
      "  property pp(property p); p; endproperty\n"
      "  sequence qs(sequence s); s; endsequence\n"
      "  assert property (ps(a));\n"
      "  assert property (pp(a |-> a));\n"
      "  cover property (qs(a ##1 a));\n"
      "  assert property (ps((@(posedge clk) a) and (@(posedge c2) a)));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoClockReport, 6, "16.16"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoClockReport, 7, "16.16"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoClockReport, 8, "16.16"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoClockReport, 9, "16.16"));
}

TEST(ClockedActualElaboration, ACheckerFormalTakesItsActualsClock) {
  ElabFixture f;
  Elaborate(
      "checker chk(property p, sequence s);\n"
      "  assert property (p);\n"
      "  assume property (p);\n"
      "  cover property (s);\n"
      "endchecker\n"
      "module m;\n"
      "  logic clk, a;\n"
      "  global clocking @(posedge clk); endclocking\n"
      "  chk c1(@(posedge clk) a, @(posedge clk) a);\n"
      "  chk c2(@($global_clock) a, @$global_clock a);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
}

TEST(ClockedActualElaboration, ACheckerFormalGivenAnUnclockedActualIsReported) {
  ElabFixture f;
  Elaborate(
      "checker chk(property p, sequence s);\n"
      "  assert property (p);\n"
      "  cover property (s);\n"
      "endchecker\n"
      "module m;\n"
      "  logic a;\n"
      "  chk c1(a, a ##1 a);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoClockReport, 2, "16.16"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoClockReport, 3, "16.16"));
}

TEST(DeterminedClockElaboration, EveryStatementKindNeedsALeadingClock) {
  ElabFixture f;
  Elaborate(
      "module m(input logic a, b, c, clk);\n"
      "  property pc; @(posedge clk) a; endproperty\n"
      "  property pu; a; endproperty\n"
      "  property q1; $rose(a) |-> ##[1:5] b; endproperty\n"
      "  property q5; @(negedge clk) b; endproperty\n"
      "  property q6; q1 and q5; endproperty\n"
      "  restrict property (a);\n"
      "  restrict property (@(posedge clk) a);\n"
      "  restrict property (pc);\n"
      "  restrict property (pu);\n"
      "  assume property (a);\n"
      "  assume property (@(posedge clk) a);\n"
      "  cover sequence (a ##1 b);\n"
      "  cover sequence (@(posedge clk) a ##1 b);\n"
      "  assert property (q6);\n"
      "  assert property ($fell(c) |=> q6);\n"
      "  assert property (q5);\n"
      "endmodule\n",
      f);
  for (uint32_t line : {7u, 10u, 11u, 13u, 15u, 16u}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNoClockReport, line, "16.16"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 6u);
}

TEST(DeterminedClockElaboration, ABodyOverAClockedSequenceDeterminesItsClock) {
  ElabFixture f;
  Elaborate(
      "module m(input logic a, b, clk);\n"
      "  sequence s2; @(negedge clk) a ##1 b; endsequence\n"
      "  property p2; not s2; endproperty\n"
      "  property pe; s2 and s2; endproperty\n"
      "  property po; s2 or s2; endproperty\n"
      "  property pa; accept_on(a) s2; endproperty\n"
      "  property pr; reject_on(a) s2; endproperty\n"
      "  property pg; s2; endproperty\n"
      "  property pi; pg; endproperty\n"
      "  property pn; not pg; endproperty\n"
      "  sequence sk; s2 ##1 b; endsequence\n"
      "  sequence sz; s2 ##0 b; endsequence\n"
      "  sequence sp; (s2); endsequence\n"
      "  property pp; (s2); endproperty\n"
      "  property pm; s2 |-> a; endproperty\n"
      "  property pd; s2 |=> a; endproperty\n"
      "  assert property (p2);\n"
      "  assert property (pe);\n"
      "  assert property (po);\n"
      "  assert property (pa);\n"
      "  assert property (pr);\n"
      "  assert property (pi);\n"
      "  assert property (pn);\n"
      "  cover property (sk);\n"
      "  cover sequence (sk);\n"
      "  cover property (sz);\n"
      "  cover sequence (sz);\n"
      "  cover property (sp);\n"
      "  assert property (pp);\n"
      "  assert property (pm);\n"
      "  assert property (pd);\n"
      "  assert property (s2);\n"
      "  restrict property (p2);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
}

TEST(DeterminedClockElaboration, ABodyOverAnUnclockedSequenceIsReported) {
  ElabFixture f;
  Elaborate(
      "module m(input logic a, b, clk);\n"
      "  sequence su; a ##1 b; endsequence\n"
      "  property un; not su; endproperty\n"
      "  property ue; su and su; endproperty\n"
      "  property uo; su or su; endproperty\n"
      "  property ua; accept_on(a) su; endproperty\n"
      "  property ur; reject_on(a) su; endproperty\n"
      "  property ug; su; endproperty\n"
      "  property ui; ug; endproperty\n"
      "  property uv; not ug; endproperty\n"
      "  sequence uk; su ##1 b; endsequence\n"
      "  sequence uz; su ##0 b; endsequence\n"
      "  sequence us; (su); endsequence\n"
      "  property up; (su); endproperty\n"
      "  property um; su |-> a; endproperty\n"
      "  property ud; su |=> a; endproperty\n"
      "  assert property (un);\n"
      "  assert property (ue);\n"
      "  assert property (uo);\n"
      "  assert property (ua);\n"
      "  assert property (ur);\n"
      "  assert property (ui);\n"
      "  assert property (uv);\n"
      "  cover property (uk);\n"
      "  cover sequence (uk);\n"
      "  cover property (uz);\n"
      "  cover sequence (uz);\n"
      "  cover property (us);\n"
      "  assert property (up);\n"
      "  assert property (um);\n"
      "  assert property (ud);\n"
      "  assert property (su);\n"
      "  restrict property (un);\n"
      "endmodule\n",
      f);
  for (uint32_t line = 17; line <= 33; ++line) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNoClockReport, line, "16.16"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 17u);
}

TEST(DeterminedClockElaboration, AStrongOrWeakBodyTakesItsSequencesClock) {
  ElabFixture f;
  Elaborate(
      "module m(input logic a, b, clk);\n"
      "  sequence s2; @(negedge clk) a ##1 b; endsequence\n"
      "  property ps; strong(s2); endproperty\n"
      "  property pw; weak(s2); endproperty\n"
      "  assert property (ps);\n"
      "  assert property (pw);\n"
      "  assert property (strong(s2));\n"
      "  assert property (weak(s2));\n"
      "endmodule\n",
      f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(DeterminedClockElaboration, EachPlaceLooksTheDeclarationUp) {
  ElabFixture f;
  Elaborate(
      "property cuq(x, c); @(posedge c) x; endproperty\n"
      "sequence cus(x, c); @(posedge c) x; endsequence\n"
      "package pk;\n"
      "  bit pk_clk;\n"
      "  property pq; @(posedge pk_clk) 1; endproperty\n"
      "  property pr(x, c); @(posedge c) x; endproperty\n"
      "endpackage\n"
      "interface i(input logic a, b, clk);\n"
      "  sequence s2; @(negedge clk) a ##1 b; endsequence\n"
      "  property p2; not s2; endproperty\n"
      "  assert property (p2);\n"
      "  assert property (a);\n"
      "endinterface\n"
      "program g(input logic a, clk);\n"
      "  property pg; @(negedge clk) a; endproperty\n"
      "  assert property (pg);\n"
      "  assert property (a);\n"
      "endprogram\n"
      "checker ck(logic a, logic clk);\n"
      "  property pg; @(negedge clk) a; endproperty\n"
      "  assert property (pg);\n"
      "  assert property (a);\n"
      "endchecker\n"
      "module m(input logic a, b, clk);\n"
      "  import pk::pr;\n"
      "  property pg; @(negedge clk) a; endproperty\n"
      "  if (1) begin : gi\n"
      "    property pgi; @(negedge clk) a; endproperty\n"
      "    sequence sgi; @(negedge clk) a; endsequence\n"
      "    assert property (pgi);\n"
      "    cover property (sgi);\n"
      "    assert property (pg);\n"
      "    assert property (a);\n"
      "  end\n"
      "  for (genvar k = 0; k < 1; k++) begin : gf\n"
      "    property pgf; @(negedge clk) a; endproperty\n"
      "    assert property (pgf);\n"
      "    assert property (pg);\n"
      "    assert property (a);\n"
      "  end\n"
      "  assert property (cuq(a, clk));\n"
      "  cover property (cus(a, clk));\n"
      "  assert property (pk::pq);\n"
      "  assert property (pr(a, clk));\n"
      "  initial begin\n"
      "    assert property (pg);\n"
      "    assert property (a);\n"
      "  end\n"
      "  always @(a) begin\n"
      "    assert property (pg);\n"
      "    assert property (a);\n"
      "  end\n"
      "  i u(a, b, clk);\n"
      "  g v(a, clk);\n"
      "  ck c(a, clk);\n"
      "endmodule\n",
      f);
  for (uint32_t line : {12u, 17u, 22u, 33u, 39u}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNoClockReport, line, "16.16"));
  }
  for (uint32_t line : {47u, 51u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "no clock is inferred",
                              line, "16.14.6"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 7u);
}

}  // namespace
