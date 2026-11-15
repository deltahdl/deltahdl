#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_placed_assertion_runs.h"

using namespace delta;

namespace {

std::string Sorted(const std::string& src) {
  SimFixture f;
  return PlacedSortedVerdicts(RunCapture(src, f));
}

const char* const kOneEdge =
    "  initial begin\n"
    "    #5 clk = 1;\n"
    "    #5 clk = 0;\n"
    "    #5 clk = 1;\n"
    "    #1 $finish;\n"
    "  end\n";

TEST(CheckerUntypedFormalRun, DISABLED_AnAssertionReadsTheWholeActual) {
  EXPECT_EQ(Sorted("checker cu(v, w, logic clk);\n"
                   "  a1: assert property (@(posedge clk) v == 6)\n"
                   "    $display(\"eq\");\n"
                   "  a2: assert property (@(posedge clk) v inside {6})\n"
                   "    $display(\"inside\");\n"
                   "  a3: assert property (@(posedge clk) v dist {6 := 1})\n"
                   "    $display(\"dist\");\n"
                   "  a4: assert property (@(posedge clk) $past(v) == 6)\n"
                   "    $display(\"past\");\n"
                   "  a5: assert property (@(posedge clk) $changed(w))\n"
                   "    $display(\"changed %0t\", $time);\n"
                   "endchecker\n"
                   "module top;\n"
                   "  logic clk = 0;\n"
                   "  int x = 6, y = 6;\n"
                   "  cu u(x, y, clk);\n"
                   "  initial #12 y = 4;\n" +
                   std::string(kOneEdge) + "endmodule\n"),
            "changed 15\ndist\ndist\neq\neq\ninside\ninside\npast\npast\n");
}

TEST(CheckerUntypedFormalRun, DISABLED_AnActionBlockReadsTheWholeActual) {
  EXPECT_EQ(Sorted("checker cu(v, logic clk);\n"
                   "  a1: assert property (@(posedge clk) 1)\n"
                   "    $display(\"act %0d\", v);\n"
                   "endchecker\n"
                   "module top;\n"
                   "  logic clk = 0;\n"
                   "  int x = 6;\n"
                   "  cu u(x, clk);\n" +
                   std::string(kOneEdge) + "endmodule\n"),
            "act 6\nact 6\n");
}

TEST(CheckerUntypedFormalRun, DISABLED_ProceduresAndAssignmentsReadIt) {
  EXPECT_EQ(Sorted("checker cu(v, logic clk);\n"
                   "  int comb, ff, asg;\n"
                   "  int decl = v;\n"
                   "  always_comb comb = v;\n"
                   "  always_ff @(posedge clk) ff <= v;\n"
                   "  initial a0: assert (v == 6) $display(\"ini\");\n"
                   "  assign asg = v;\n"
                   "endchecker\n"
                   "module top;\n"
                   "  parameter int P = 6;\n"
                   "  logic clk = 0;\n"
                   "  cu u(P, clk);\n"
                   "  initial #20 $display(\"%0d %0d %0d %0d\", u.decl, "
                   "u.comb, u.ff, u.asg);\n"
                   "  initial begin #5 clk = 1; #5 clk = 0; #5 clk = 1; #10 "
                   "$finish; end\n"
                   "endmodule\n"),
            "6 6 6 6\nini\n");
}

TEST(CheckerUntypedFormalRun, DISABLED_ANestedCheckerSequenceOrPropertyGetsIt) {
  EXPECT_EQ(Sorted("checker inner(v2, logic clk);\n"
                   "  always_ff @(posedge clk) $display(\"inner %0d\", v2);\n"
                   "endchecker\n"
                   "checker outer(v, logic clk);\n"
                   "  sequence s(q);\n    q == 6;\n  endsequence\n"
                   "  property pr(q);\n    q == 6;\n  endproperty\n"
                   "  inner i(v, clk);\n"
                   "  a1: assert property (@(posedge clk) s(v)) "
                   "$display(\"seq\");\n"
                   "  a2: assert property (@(posedge clk) pr(v)) "
                   "$display(\"prop\");\n"
                   "endchecker\n"
                   "module top;\n"
                   "  logic clk = 0;\n"
                   "  int x = 6;\n"
                   "  outer u(x, clk);\n" +
                   std::string(kOneEdge) + "endmodule\n"),
            "inner 6\ninner 6\nprop\nprop\nseq\nseq\n");
}

const char* const kShowChecker =
    "checker show(v, logic clk);\n"
    "  always_ff @(posedge clk) $display(\"%m %0d\", v);\n"
    "endchecker\n";

TEST(CheckerUntypedFormalRun, DISABLED_EachKindOfActualIsReadWhole) {
  EXPECT_EQ(Sorted(std::string(kShowChecker) +
                   "checker showr(v, logic clk);\n"
                   "  always_ff @(posedge clk) $display(\"%m %0.1f\", v);\n"
                   "endchecker\n"
                   "module top;\n"
                   "  parameter int P = 6;\n"
                   "  logic clk = 0;\n"
                   "  int x = 6;\n"
                   "  logic [7:0] pv = 8'ha6;\n"
                   "  logic signed [7:0] sv = -8'sd6;\n"
                   "  real r = 2.5;\n"
                   "  struct packed { logic [7:0] f; logic g; } st = "
                   "{8'h96, 1'b0};\n"
                   "  show u_int(x, clk);\n"
                   "  show u_vec(pv, clk);\n"
                   "  show u_sgn(sv, clk);\n"
                   "  showr u_real(r, clk);\n"
                   "  show u_expr(x + 4, clk);\n"
                   "  show u_part(pv[7:4], clk);\n"
                   "  show u_mem(st.f, clk);\n"
                   "  show u_par(P, clk);\n"
                   "  initial begin #5 clk = 1; #1 $finish; end\n"
                   "endmodule\n"),
            "top.u_expr 10\ntop.u_int 6\ntop.u_mem 150\ntop.u_par 6\n"
            "top.u_part 10\ntop.u_real 2.5\ntop.u_sgn -6\ntop.u_vec 166\n");
}

TEST(CheckerUntypedFormalRun, DISABLED_EachConnectionFormReadsItWhole) {
  EXPECT_EQ(Sorted(std::string(kShowChecker) +
                   "module top;\n"
                   "  logic clk = 0;\n"
                   "  int v = 6;\n"
                   "  show u_pos(v, clk);\n"
                   "  show u_named(.v(v), .clk(clk));\n"
                   "  show u_implicit(.v, .clk);\n"
                   "  show u_wild(.*);\n"
                   "  initial begin #5 clk = 1; #1 $finish; end\n"
                   "endmodule\n"),
            "top.u_implicit 6\ntop.u_named 6\ntop.u_pos 6\ntop.u_wild 6\n");
}

const char* const kShowBody =
    "  always_ff @(posedge clk) $display(\"%m %0d\", v);\n";

std::string ShowNamed(const std::string& name) {
  return "checker " + name + "(v, logic clk);\n" + kShowBody + "endchecker\n";
}

TEST(CheckerUntypedFormalRun, DISABLED_ACheckerDeclaredAnywhereReadsItWhole) {
  EXPECT_EQ(Sorted(ShowNamed("s_unit") + "package pk;\n" + ShowNamed("s_pkg") +
                   "endpackage\n"
                   "interface ifc(input logic clk);\n"
                   "  int x = 6;\n" +
                   ShowNamed("s_ifc") +
                   "  s_ifc u(x, clk);\n"
                   "endinterface\n"
                   "program prg(input logic clk);\n"
                   "  int x = 6;\n" +
                   ShowNamed("s_prg") +
                   "  s_prg u(x, clk);\n"
                   "endprogram\n"
                   "module top;\n"
                   "  logic clk = 0;\n"
                   "  int x = 6;\n" +
                   ShowNamed("s_mod") +
                   "  s_mod u_mod(x, clk);\n"
                   "  pk::s_pkg u_pkg(x, clk);\n"
                   "  s_unit u_unit(x, clk);\n"
                   "  ifc i(clk);\n"
                   "  prg p(clk);\n"
                   "  initial begin #5 clk = 1; #1 $finish; end\n"
                   "endmodule\n"),
            "top.i.u 6\ntop.p.u 6\ntop.u_mod 6\ntop.u_pkg 6\ntop.u_unit 6\n");
}

TEST(CheckerUntypedFormalRun, DISABLED_AGenerateBlocksCheckerReadsItWhole) {
  EXPECT_EQ(Sorted("module top;\n"
                   "  logic clk = 0;\n"
                   "  int x = 6;\n"
                   "  if (1) begin : g\n" +
                   ShowNamed("s_gen") +
                   "    s_gen u(x, clk);\n"
                   "  end\n"
                   "  initial begin #5 clk = 1; #1 $finish; end\n"
                   "endmodule\n"),
            "top.g.u 6\n");
}

TEST(CheckerUntypedFormalRun, ATypedFormalReadsTheWholeActual) {
  EXPECT_EQ(Sorted("checker ti(int v, logic [7:0] w, logic clk);\n"
                   "  always_ff @(posedge clk) $display(\"%0d %0d\", v, w);\n"
                   "  a1: assert property (@(posedge clk) v == 6) "
                   "$display(\"eq\");\n"
                   "endchecker\n"
                   "module top;\n"
                   "  logic clk = 0;\n"
                   "  int x = 6;\n"
                   "  logic [7:0] pv = 8'ha6;\n"
                   "  ti u(x, pv, clk);\n"
                   "  initial begin #5 clk = 1; #1 $finish; end\n"
                   "endmodule\n"),
            "6 166\neq\n");
}

}  // namespace
