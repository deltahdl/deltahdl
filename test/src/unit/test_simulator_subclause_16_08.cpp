#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_sampling_bench.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(NamedSequenceLowering, EndPointVariableIsCreated) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, a, b;\n"
      "  sequence ab;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  EXPECT_NE(f.ctx.FindSequenceDecl("ab"), nullptr);
  auto* ep = f.ctx.FindVariable("__seq_ab");
  ASSERT_NE(ep, nullptr);
  EXPECT_TRUE(ep->is_event);
}

TEST(NamedSequenceLowering, MultipleSequencesEachGetEndPoint) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, a, b, c;\n"
      "  sequence first;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  sequence second;\n"
      "    @(posedge clk) b ##1 c;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  EXPECT_NE(f.ctx.FindVariable("__seq_first"), nullptr);
  EXPECT_NE(f.ctx.FindVariable("__seq_second"), nullptr);
}

std::string InstanceSource(const std::string& decls) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic req = 0;\n"
         "  logic gnt = 0;\n"
         "  int hits = 0;\n"
         "  int last = 0;\n"
         "  always #5 clk = ~clk;\n" +
         decls +
         "  initial begin\n"
         "    #10 req = 1;\n"
         "    #10 req = 0;\n"
         "    #10 gnt = 1;\n"
         "    #30 gnt = 0;\n"
         "    #30 $finish;\n"
         "  end\n"
         "  initial forever begin\n"
         "    wait (rule.triggered);\n"
         "    hits = hits + 1;\n"
         "    last = $time;\n"
         "    @(posedge clk);\n"
         "  end\n"
         "endmodule\n";
}

TEST(NamedSequenceInstance, ClocklessSequenceInheritsTheInstantiatingClock) {
  SimFixture f;
  auto* hits = RunAndFindVar(InstanceSource("  sequence s;\n"
                                            "    req ##2 gnt;\n"
                                            "  endsequence\n"
                                            "  sequence rule;\n"
                                            "    @(posedge clk) s;\n"
                                            "  endsequence\n"),
                             f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 35u);
}

TEST(NamedSequenceInstance, DelayBeforeAnInstanceAddsToItsLeadingDelay) {
  SimFixture f;
  auto* hits = RunAndFindVar(InstanceSource("  sequence s;\n"
                                            "    ##1 gnt;\n"
                                            "  endsequence\n"
                                            "  sequence rule;\n"
                                            "    @(posedge clk) req ##1 s;\n"
                                            "  endsequence\n"),
                             f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 35u);
}

TEST(NamedSequenceInstance, PositionalActualsSubstituteForTheFormals) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(InstanceSource("  sequence win(x, y, lo, hi);\n"
                                   "    x ##[lo:hi] y;\n"
                                   "  endsequence\n"
                                   "  sequence rule;\n"
                                   "    @(posedge clk) win(req, gnt, 3, $);\n"
                                   "  endsequence\n"),
                    f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 55u);
}

TEST(NamedSequenceInstance, NamedActualsSubstituteForTheFormals) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      InstanceSource("  sequence win(x, y, lo, hi);\n"
                     "    x ##[lo:hi] y;\n"
                     "  endsequence\n"
                     "  sequence rule;\n"
                     "    @(posedge clk) win(.hi(2), .lo(2), .y(gnt && !req), "
                     ".x(req));\n"
                     "  endsequence\n"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 35u);
}

TEST(NamedSequenceInstance, InstanceMayPrecedeTheDeclaration) {
  SimFixture f;
  auto* hits = RunAndFindVar(InstanceSource("  sequence rule;\n"
                                            "    @(posedge clk) later;\n"
                                            "  endsequence\n"
                                            "  sequence later;\n"
                                            "    req ##2 gnt;\n"
                                            "  endsequence\n"),
                             f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 35u);
}

TEST(NamedSequenceInstance, AnOmittedFormalTakesItsDefault) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  bit [0:9] av = 10'b1010010000, bv = 10'b0101001010;\n"
      "  bit a, b; assign a = av[0]; assign b = bv[0];\n"
      "  always @(negedge clk) begin av <= av << 1; bv <= bv << 1; end\n"
      "  int cdef = 0;\n"
      "  sequence s_def(x, y = b); x ##1 y; endsequence\n"
      "  cover property (@(posedge clk) s_def(a)) cdef++;\n"
      "  initial #98 $display(\"cdef=%0d\", cdef);\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("cdef=3\n"), std::string::npos);
}

TEST(NamedSequenceInstance, AnOmittedDelayFormalTakesItsDefault) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  bit [0:9] av = 10'b1010010000, bv = 10'b0101001010;\n"
      "  bit a, b; assign a = av[0]; assign b = bv[0];\n"
      "  always @(negedge clk) begin av <= av << 1; bv <= bv << 1; end\n"
      "  int c1 = 0;\n"
      "  sequence s_def2(x, shortint d = 3); x ##d b; endsequence\n"
      "  cover property (@(posedge clk) s_def2(a)) c1++;\n"
      "  initial #98 $display(\"c1=%0d\", c1);\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("c1=2\n"), std::string::npos);
}

TEST(NamedSequenceInstance, APackageSequenceIsInstantiatedByImportAndByScope) {
  SimFixture f;
  std::string out = RunCapture(
      "package pk;\n"
      "  sequence s2(x, y); x ##1 y; endsequence\n"
      "endpackage\n"
      "import pk::*;\n"
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  bit [0:9] av = 10'b0100100000, bv = 10'b0010000000;\n"
      "  bit a, b; assign a = av[0]; assign b = bv[0];\n"
      "  always @(negedge clk) begin av <= av << 1; bv <= bv << 1; end\n"
      "  int p = 0, f = 0, p2 = 0, f2 = 0;\n"
      "  assert property (@(posedge clk) a |-> s2(a, b)) p++; else f++;\n"
      "  assert property (@(posedge clk) a |-> pk::s2(a, b)) p2++; else f2++;\n"
      "  initial #98 $display(\"p=%0d f=%0d p2=%0d f2=%0d\", p, f, p2, f2);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "p=9 f=1 p2=9 f2=1\n");
}

TEST(NamedSequenceInstance, APackageSequenceIsNamedThroughTheScopeAlone) {
  SimFixture f;
  std::string out = RunCapture(
      "package pk;\n"
      "  sequence s; 1'b1 ##1 1'b1; endsequence\n"
      "endpackage\n"
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  bit [0:9] av = 10'b0100100000;\n"
      "  bit a; assign a = av[0];\n"
      "  always @(negedge clk) av <= av << 1;\n"
      "  int p = 0, f = 0;\n"
      "  assert property (@(posedge clk) a |-> pk::s) p++; else f++;\n"
      "  initial #98 $display(\"p=%0d f=%0d\", p, f);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "p=10 f=0\n");
}

TEST(NamedSequenceInstance, AnEventFormalLeftToItsDefaultClocksTheStatement) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  logic a = 1;\n"
      "  int c3 = 0, c4 = 0;\n"
      "  sequence s_p(untyped x, event e = posedge clk); @(e) x; endsequence\n"
      "  cover property (s_p(a)) c3++;\n"
      "  cover property (s_p(a, posedge clk)) c4++;\n"
      "  initial #98 $display(\"c3=%0d c4=%0d\", c3, c4);\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("c3=10 c4=10\n"), std::string::npos);
}

std::string RunInterfaceSequence(const std::string& seq,
                                 const std::string& inst) {
  SimFixture f;
  return RunCapture(
      "interface bus(input logic clk);\n"
      "  logic req, gnt;\n" +
          seq +
          "endinterface\n"
          "module t;\n"
          "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
          "  bit [0:9] av = 10'b0100100000, bv = 10'b0010000000;\n"
          "  always @(negedge clk) begin av <= av << 1; bv <= bv << 1; end\n"
          "  bus u(clk);\n"
          "  assign u.req = av[0]; assign u.gnt = bv[0];\n"
          "  int p = 0, f = 0;\n"
          "  assert property (@(posedge clk) u.req |-> " +
          inst +
          ") p++;\n"
          "    else begin f++; $display(\"fail at %0t\", $time); end\n"
          "  initial #98 $display(\"p=%0d f=%0d\", p, f);\n"
          "endmodule\n",
      f);
}

TEST(NamedSequenceInstance,
     AnInterfaceSequenceIsInstantiatedThroughAnInstance) {
  EXPECT_EQ(
      RunInterfaceSequence("  sequence s; req ##1 gnt; endsequence\n", "u.s"),
      "fail at 55\np=9 f=1\n");
}

TEST(NamedSequenceInstance,
     AnInterfaceSequenceKeepsItsFormalsAndLocalsThroughAnInstance) {
  EXPECT_EQ(
      RunInterfaceSequence("  sequence s(g); bit v; (1, v = req) ##1 (v && g); "
                           "endsequence\n",
                           "u.s(u.gnt)"),
      "fail at 55\np=9 f=1\n");
}

std::string RunEventActualCase(const std::string& decls,
                               const std::string& covers) {
  SimFixture f;
  return RunCapture(
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  logic en = 0; initial #42 en = 1;\n"
      "  logic h = 0; initial begin #22 h = 1; #40 h = 0; end\n"
      "  logic a = 1;\n"
      "  int c1 = 0, c2 = 0;\n" +
          decls + covers +
          "  initial #98 $display(\"c1=%0d c2=%0d\", c1, c2);\n"
          "endmodule\n",
      f);
}

TEST(NamedSequenceInstance, AGuardedEventActualClocksWhereTheGuardHolds) {
  std::string out = RunEventActualCase(
      "  sequence s_g(untyped x, event e); @(e) x; endsequence\n",
      "  cover property (s_g(a, posedge clk iff en)) c1++;\n"
      "  cover property (s_g(a, posedge clk)) c2++;\n");
  EXPECT_NE(out.find("c1=6 c2=10\n"), std::string::npos);
}

TEST(NamedSequenceInstance, AGuardedEventDefaultClocksWhereTheGuardHolds) {
  std::string out = RunEventActualCase(
      "  sequence s_d(untyped x, event e = posedge clk iff en);\n"
      "    @(e) x;\n"
      "  endsequence\n",
      "  cover property (s_d(a)) c1++;\n"
      "  cover property (s_d(a, posedge clk)) c2++;\n");
  EXPECT_NE(out.find("c1=6 c2=10\n"), std::string::npos);
}

TEST(NamedSequenceInstance, AnOrEventDefaultClocksOnEitherEvent) {
  std::string out = RunEventActualCase(
      "  sequence s_o(untyped x, event e = posedge clk or negedge clk);\n"
      "    @(e) x;\n"
      "  endsequence\n",
      "  cover property (s_o(a)) c1++;\n"
      "  cover property (s_o(a, edge clk)) c2++;\n");
  EXPECT_NE(out.find("c1=19 c2=19\n"), std::string::npos);
}

TEST(NamedSequenceInstance, AClocksGuardHoldsBesideTheActualsGuard) {
  std::string out = RunEventActualCase(
      "  sequence s_c(untyped x, event e, untyped g);\n"
      "    @(e iff g) x;\n"
      "  endsequence\n",
      "  cover property (s_c(a, posedge clk iff en, h)) c1++;\n"
      "  cover property (s_c(a, posedge clk, h)) c2++;\n");
  EXPECT_NE(out.find("c1=2 c2=4\n"), std::string::npos);
}

TEST(NamedSequenceInstance, APropertyClockedOnItsEventFormalTakesEither) {
  std::string out = RunEventActualCase(
      "  property p_g(untyped x, event e); @(e) x; endproperty\n",
      "  cover property (p_g(a, posedge clk iff en)) c1++;\n"
      "  cover property (p_g(a, posedge clk or negedge clk)) c2++;\n");
  EXPECT_NE(out.find("c1=6 c2=19\n"), std::string::npos);
}

TEST(NamedSequenceInstance, AnUntypedFormalsActualIsSelfDetermined) {
  std::string out = RunEventActualCase(
      "  logic [3:0] p = 4'hF, q = 4'h1;\n"
      "  sequence s_w(x); @(posedge clk) x == 0; endsequence\n"
      "  property p_w(x); @(posedge clk) x == 0; endproperty\n",
      "  cover property (s_w(p + q)) c1++;\n"
      "  cover property (p_w(p + q)) c2++;\n");
  EXPECT_NE(out.find("c1=10 c2=10\n"), std::string::npos) << out;
}

TEST(NamedSequenceInstance, EveryOperatorActualIsSelfDetermined) {
  std::string out = RunEventActualCase(
      "  logic [3:0] p = 4'hF, q = 4'h1;\n"
      "  real r = 1.25;\n"
      "  sequence s_w(x); @(posedge clk) x == 0; endsequence\n"
      "  sequence s_r(x); @(posedge clk) x > 1.5; endsequence\n"
      "  int c3 = 0;\n",
      "  cover property (s_w(~p)) c1++;\n"
      "  cover property (s_w(1 ? p + q : 0)) c2++;\n"
      "  cover property (s_r(r + 0.5)) c3++;\n"
      "  initial #99 $display(\"c3=%0d\", c3);\n");
  EXPECT_NE(out.find("c1=10 c2=10\n"), std::string::npos) << out;
  EXPECT_NE(out.find("c3=10\n"), std::string::npos) << out;
}

std::string RunScopeCase(const std::string& decls, const std::string& gen) {
  SimFixture f;
  return RunCapture(
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  logic d = 1, e = 1, k = 0;\n"
      "  int c1 = 0, c2 = 0;\n" +
          decls +
          "  if (1) begin : g\n"
          "    logic d = 0, e = 0, k = 1;\n" +
          gen +
          "  end\n"
          "  initial #98 $display(\"c1=%0d c2=%0d\", c1, c2);\n"
          "endmodule\n",
      f);
}

TEST(NamedSequenceInstance, AnActualsNamesResolveWhereTheInstanceStands) {
  EXPECT_EQ(RunScopeCase("  sequence s_a(x); @(posedge clk) x; endsequence\n",
                         "    cover property (s_a(k)) c1++;\n"
                         "    cover property (s_a(!k)) c2++;\n"),
            "c1=10 c2=0\n");
}

TEST(NamedSequenceInstance,
     DISABLED_ABodysNamesResolveWhereTheSequenceIsDeclared) {
  EXPECT_EQ(RunScopeCase("  sequence s_b; @(posedge clk) e; endsequence\n"
                         "  sequence s_n; @(posedge clk) !d; endsequence\n",
                         "    cover property (s_b) c1++;\n"
                         "    cover property (s_n) c2++;\n"),
            "c1=10 c2=0\n");
}

TEST(NamedSequenceInstance,
     DISABLED_ADefaultActualResolvesWhereTheSequenceIsDeclared) {
  EXPECT_EQ(
      RunScopeCase("  sequence s_d(x = d); @(posedge clk) x; endsequence\n",
                   "    cover property (s_d()) c1++;\n"
                   "    cover property (s_d(d)) c2++;\n"),
      "c1=10 c2=0\n");
}

TEST(NamedSequenceInstance, ATypeAppliesToEachUntypedFormalAfterIt) {
  std::string out = RunEventActualCase(
      "  logic [3:0] w = 4'h2;\n"
      "  sequence s_t(bit x, y, int z); @(posedge clk) x && y == 0 && z == 2;\n"
      "  endsequence\n"
      "  sequence s_u(x, y); @(posedge clk) x && y == 0; endsequence\n",
      "  cover property (s_t(1, w, w)) c1++;\n"
      "  cover property (s_u(1, w)) c2++;\n");
  EXPECT_NE(out.find("c1=10 c2=0\n"), std::string::npos) << out;
}

TEST(NamedSequenceInstance, AnActualIsParenthesizedWhereItIsSubstituted) {
  std::string out = RunEventActualCase(
      "  logic b = 0, z = 0;\n"
      "  sequence s_p(x); @(posedge clk) x & z; endsequence\n"
      "  sequence s_q(x); @(posedge clk) !x; endsequence\n",
      "  cover property (s_p(a | b)) c1++;\n"
      "  cover property (s_q(a && b)) c2++;\n");
  EXPECT_NE(out.find("c1=0 c2=10\n"), std::string::npos) << out;
}

TEST(NamedSequenceInstance, AnInstanceReadsALocalInWhoseScopeItStands) {
  std::string out = RunEventActualCase(
      "  sequence s_eq(x); x == 3; endsequence\n"
      "  sequence s_l; int v; @(posedge clk) (1, v = 3) ##1 s_eq(v);\n"
      "  endsequence\n"
      "  sequence s_m; int v; @(posedge clk) (1, v = 4) ##1 s_eq(v);\n"
      "  endsequence\n",
      "  cover property (s_l) c1++;\n"
      "  cover property (s_m) c2++;\n");
  EXPECT_NE(out.find("c1=9 c2=0\n"), std::string::npos) << out;
}

std::string EmptyListBench(const std::string& outside,
                           const std::string& items) {
  return outside +
         "module top;\n"
         "  logic clk = 0, a = 1, b = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  " +
         items +
         "\n"
         "  initial begin #20 b = 1; #30 $finish; end\n"
         "endmodule\n";
}

std::string EmptyListAssertion(const std::string& instance) {
  return "assert property (@(posedge clk) " + instance +
         ") $display(\"pass %0t\", $time); else $display(\"fail %0t\", "
         "$time);";
}

void ExpectRunsAsTheBody(const std::string& src) {
  ExpectLines(src, "pass ", "25 35 45");
  ExpectLines(src, "fail ", "15");
}

TEST(NamedSequenceInstance, AnEmptyListInstanceMatchesWhereItsBodyDoes) {
  for (const char* decl : {"sequence s(); a ##1 b; endsequence",
                           "sequence s; a ##1 b; endsequence"}) {
    for (const char* instance : {"s()", "s"}) {
      ExpectRunsAsTheBody(EmptyListBench(
          "", std::string(decl) + "\n  " + EmptyListAssertion(instance)));
    }
  }
}

struct EmptyListPlace {
  std::string place;
  std::string outside;
  std::string items;
};

std::vector<EmptyListPlace> EmptyListPlaces() {
  const std::string kDecl = "sequence s(); a ##1 b; endsequence";
  const std::string kHere = EmptyListAssertion("s()");
  const std::string kVars = "  bit a = 1, b = 0;\n  " + kDecl + "\n";
  return {
      {"interface",
       "interface ifc(input logic clk, a, b);\n  " + kDecl + "\nendinterface\n",
       "ifc i(clk, a, b);\n  " + EmptyListAssertion("i.s()")},
      {"program",
       "program pg(input logic clk, a, b);\n  " + kDecl + "\n  " + kHere +
           "\nendprogram\n",
       "pg p(clk, a, b);"},
      {"clocking block", "",
       "clocking cb @(posedge clk);\n    " + kDecl + "\n  endclocking\n  " +
           EmptyListAssertion("cb.s()")},
      {"package by name", "package pk;\n" + kVars + "endpackage\n",
       "initial #20 pk::b = 1;\n  " + EmptyListAssertion("pk::s()")},
      {"package by import", "package pk;\n" + kVars + "endpackage\n",
       "import pk::s;\n  initial #20 pk::b = 1;\n  " + kHere},
      {"checker",
       "checker ck(logic clk, logic a, logic b);\n  " + kDecl + "\n  " + kHere +
           "\nendchecker\n",
       "ck k(clk, a, b);"},
      {"generate", "",
       "if (1) begin : g\n    " + kDecl + "\n    " + kHere + "\n  end"}};
}

TEST(NamedSequenceInstance, EveryPlaceRunsAnEmptyListInstanceAsItsBody) {
  for (const auto& placed : EmptyListPlaces()) {
    SCOPED_TRACE(placed.place);
    ExpectRunsAsTheBody(EmptyListBench(placed.outside, placed.items));
  }
}

TEST(NamedSequenceInstance, DISABLED_ACompilationUnitEmptyListInstanceRuns) {
  ExpectRunsAsTheBody(EmptyListBench(
      "bit a = 1, b = 0;\nsequence s(); a ##1 b; endsequence\n",
      "initial #20 $unit::b = 1;\n  " + EmptyListAssertion("s()")));
}

}  // namespace
