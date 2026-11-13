#include <gtest/gtest.h>

#include "helpers_marked_reports.h"

using namespace delta;

namespace {

constexpr const char* kBelowOne =
    "the number_of_ticks of $past shall be 1 or greater";

constexpr const char* kNotConstant =
    "the number_of_ticks of $past shall be an elaboration-time constant "
    "expression";

void ExpectBelowOne(const MarkedSource& marked) {
  ExpectMarkedReports(marked, kBelowOne, "16.9.3");
}

TEST(PastTicksCount, ANegativeOrFoldedNegativeCountIsReported) {
  ExpectBelowOne({"module assertions",
                  "module m;\n"
                  "  logic clk, a, b;\n"
                  "  a1: assert property (@(posedge clk) $past(a, -1) == b);\n"
                  "  a2: assert property (@(posedge clk) $past(a, 1-3) == b);\n"
                  "  a3: assert property (@(posedge clk) $past(a, 4-3) == b);\n"
                  "endmodule\n",
                  {"a1:", "a2:"},
                  {"a3:"}});
}

TEST(PastTicksCount, AConstantNamedCountIsJudgedByItsValue) {
  ExpectBelowOne(
      {"localparams and package parameters",
       "package pk;\n"
       "  parameter int P = 0;\n"
       "  parameter int Q = 2;\n"
       "endpackage\n"
       "module m;\n"
       "  localparam int Z = 0;\n"
       "  localparam int T = 3;\n"
       "  logic clk, a, b;\n"
       "  a1: assert property (@(posedge clk) $past(a, Z) == b);\n"
       "  a2: assert property (@(posedge clk) $past(a, T) == b);\n"
       "  a3: assert property (@(posedge clk) $past(a, pk::P) == b);\n"
       "  a4: assert property (@(posedge clk) $past(a, pk::Q) == b);\n"
       "endmodule\n",
       {"a1:", "a3:"},
       {"a2:", "a4:"}});
}

TEST(PastTicksCount, ACountInAProcedureOrFunctionIsHeldToTheRule) {
  const char* const kSrc =
      "module m;\n"
      "  logic clk, a, x, y, z, c0, c2, i0, i2;\n"
      "  int k;\n"
      "  default clocking @(posedge clk); endclocking\n"
      "  always @(posedge clk) x <= $past(a, 0);\n"
      "  always @(posedge clk) y <= $past(a, k);\n"
      "  always @(posedge clk) z <= $past(a, 2);\n"
      "  always_comb c0 = $past(a, 0);\n"
      "  always_comb c2 = $past(a, 2);\n"
      "  initial i0 = $past(a, 0);\n"
      "  initial i2 = $past(a, 2);\n"
      "  function automatic logic f1(); return $past(a, 0); endfunction\n"
      "  function automatic logic f2(); return $past(a, 2); endfunction\n"
      "endmodule\n";
  ExpectBelowOne(
      {"module procedures and functions",
       kSrc,
       {"x <= $past(a, 0)", "c0 = $past(a, 0)", "i0 = $past(a, 0)", "f1();"},
       {"z <= $past(a, 2)", "c2 = $past(a, 2)", "i2 = $past(a, 2)", "f2();"}});
  ExpectMarkedReports({"a variable count", kSrc, {"y <= $past(a, k)"}, {}},
                      kNotConstant, "16.9.3");
}

TEST(PastTicksCount, ACountInADeclarationIsHeldToTheRule) {
  const MarkedSource kPlaces[] = {
      {"module property",
       "module m;\n"
       "  logic clk, a, b;\n"
       "  property p1; @(posedge clk) $past(a, 0) == b; endproperty\n"
       "  property p2; @(posedge clk) $past(a, 2) == b; endproperty\n"
       "endmodule\n",
       {"property p1;"},
       {"property p2;"}},
      {"interface",
       "interface ifc(input logic clk, a, b);\n"
       "  sequence s1; @(posedge clk) b ##1 $past(a, 0); endsequence\n"
       "  sequence s2; @(posedge clk) b ##1 $past(a, 2); endsequence\n"
       "  i1: assert property (@(posedge clk) $past(a, 0) == b);\n"
       "  i2: assert property (@(posedge clk) $past(a, 2) == b);\n"
       "endinterface\n"
       "module m;\n"
       "  logic clk, a, b;\n"
       "  ifc i(clk, a, b);\n"
       "endmodule\n",
       {"sequence s1;", "i1:"},
       {"sequence s2;", "i2:"}},
      {"checker",
       "checker ck(logic clk, logic a, logic b);\n"
       "  sequence s1; @(posedge clk) b ##1 $past(a, 0); endsequence\n"
       "  sequence s2; @(posedge clk) b ##1 $past(a, 2); endsequence\n"
       "  c1: assert property (@(posedge clk) $past(a, 0) == b);\n"
       "  c2: assert property (@(posedge clk) $past(a, 2) == b);\n"
       "endchecker\n"
       "module m;\n"
       "  logic clk, a, b;\n"
       "  ck k(clk, a, b);\n"
       "endmodule\n",
       {"sequence s1;", "c1:"},
       {"sequence s2;", "c2:"}},
      {"program",
       "program pg(input logic clk, a, b);\n"
       "  sequence s1; @(posedge clk) b ##1 $past(a, 0); endsequence\n"
       "  sequence s2; @(posedge clk) b ##1 $past(a, 2); endsequence\n"
       "endprogram\n"
       "module m;\n"
       "  logic clk, a, b;\n"
       "  pg p(clk, a, b);\n"
       "endmodule\n",
       {"sequence s1;"},
       {"sequence s2;"}}};
  for (const MarkedSource& place : kPlaces) ExpectBelowOne(place);
}

TEST(PastTicksCount, DISABLED_ACountInAGenerateBlockIsHeldToTheRule) {
  ExpectBelowOne({"generate blocks",
                  "module m;\n"
                  "  logic clk, a, b;\n"
                  "  if (1) begin : g\n"
                  "    g1: assert property (@(posedge clk) $past(a, 0) == b);\n"
                  "    g2: assert property (@(posedge clk) $past(a, 2) == b);\n"
                  "  end\n"
                  "  for (genvar j = 0; j < 1; j++) begin : h\n"
                  "    h1: assert property (@(posedge clk) $past(a, j) == b);\n"
                  "    h2: assert property (@(posedge clk) $past(a, 0) == b);\n"
                  "    h3: assert property (@(posedge clk) $past(a, 2) == b);\n"
                  "  end\n"
                  "  for (genvar n = 1; n < 3; n++) begin : u\n"
                  "    u1: assert property (@(posedge clk) $past(a, n) == b);\n"
                  "  end\n"
                  "endmodule\n",
                  {"g1:", "h1:", "h2:"},
                  {"g2:", "h3:", "u1:"}});
}

TEST(PastTicksCount, DISABLED_ACountInAContinuousAssignmentIsHeldToTheRule) {
  ExpectBelowOne({"continuous assignments",
                  "module m;\n"
                  "  logic clk, a, x, y;\n"
                  "  default clocking @(posedge clk); endclocking\n"
                  "  assign x = $past(a, 0);\n"
                  "  assign y = $past(a, 2);\n"
                  "endmodule\n",
                  {"x = $past(a, 0)"},
                  {"y = $past(a, 2)"}});
}

TEST(PastTicksCount, DISABLED_ACountInAPackageOrClassIsHeldToTheRule) {
  ExpectBelowOne(
      {"packages and classes",
       "package pk;\n"
       "  bit clk, a;\n"
       "  sequence ps0(bit c); @(posedge c) $past(a, 0); endsequence\n"
       "  sequence ps1(bit c); @(posedge c) $past(a, 0); endsequence\n"
       "  sequence ps2(bit c); @(posedge c) $past(a, 2); endsequence\n"
       "  function automatic bit pf0();"
       " return $past(a, 0, 1'b1, @(posedge clk)); endfunction\n"
       "  function automatic bit pf2();"
       " return $past(a, 2, 1'b1, @(posedge clk)); endfunction\n"
       "endpackage\n"
       "class C;\n"
       "  bit clk, a;\n"
       "  function bit m0(); return $past(a, 0, 1'b1, @(posedge clk));"
       " endfunction\n"
       "  function bit m2(); return $past(a, 2, 1'b1, @(posedge clk));"
       " endfunction\n"
       "endclass\n"
       "module m;\n"
       "  logic clk;\n"
       "  a1: assert property (pk::ps1(clk));\n"
       "  a2: assert property (pk::ps2(clk));\n"
       "endmodule\n",
       {"sequence ps0(", "sequence ps1(", "pf0();", "m0();"},
       {"sequence ps2(", "pf2();", "m2();", "a2:"}});
}

TEST(PastTicksCount, DISABLED_AFormalCountIsJudgedByEachActual) {
  ExpectBelowOne({"sequence and property formals",
                  "module m;\n"
                  "  logic clk, a, b;\n"
                  "  sequence s(int n); a ##1 $past(b, n); endsequence\n"
                  "  property p(int n); $past(b, n) == a; endproperty\n"
                  "  a1: assert property (@(posedge clk) s(2));\n"
                  "  a2: assert property (@(posedge clk) s(0));\n"
                  "  a3: assert property (@(posedge clk) p(2));\n"
                  "  a4: assert property (@(posedge clk) p(0));\n"
                  "endmodule\n",
                  {"a2:", "a4:"},
                  {"sequence s(", "property p(", "a1:", "a3:"}});
}

}  // namespace
