#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kDollarParam =
    "holds '$', so it may stand only where '$' itself may";

void ExpectDollarParamReportedOnlyOn(const ElabFixture& f,
                                     std::initializer_list<uint32_t> reported,
                                     std::initializer_list<uint32_t> accepted) {
  for (uint32_t line : reported) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kDollarParam, line, "6.20.7"))
        << line;
  }
  for (uint32_t line : accepted) {
    EXPECT_FALSE(
        ReportedError(f.diag.Diagnostics(), kDollarParam, line, "6.20.7"))
        << line;
  }
}

TEST(DollarConstantElaboration, DollarParameterIsAnErrorAsAnOrdinaryOperand) {
  ElabFixture f;
  Elaborate(
      "module sub #(parameter N = 1)(input int a);\n"
      "endmodule\n"
      "module top;\n"
      "  parameter P = $;\n"
      "  parameter Q = 4;\n"
      "  logic [7:0] w1, w2, x;\n"
      "  int n, g[4];\n"
      "  function int f(int v);\n"
      "    return v;\n"
      "  endfunction\n"
      "  function int fp();\n"
      "    return P;\n"
      "  endfunction\n"
      "  function int fq();\n"
      "    return Q;\n"
      "  endfunction\n"
      "  assign w1 = P;\n"
      "  assign w2 = Q;\n"
      "  int z = P;\n"
      "  int zq = Q;\n"
      "  logic [P:0] v;\n"
      "  logic [Q:0] vq;\n"
      "  int c[P - 1];\n"
      "  int cq[Q - 1];\n"
      "  sub u1(.a(P));\n"
      "  sub u2(.a(Q));\n"
      "  defparam u1.N = P;\n"
      "  defparam u2.N = Q;\n"
      "  initial begin\n"
      "    x = P + 1;\n"
      "    x = Q + 1;\n"
      "    x = f(P);\n"
      "    x = f(Q);\n"
      "    if (n > P) x = 1;\n"
      "    if (n > Q) x = 1;\n"
      "    g[P] = 1;\n"
      "    g[Q - 4] = 1;\n"
      "    case (n)\n"
      "      P: x = 1;\n"
      "      Q: x = 2;\n"
      "    endcase\n"
      "  end\n"
      "  if (P == 0) begin : gp\n"
      "  end\n"
      "  if (Q == 0) begin : gq\n"
      "  end\n"
      "endmodule\n",
      f);
  ExpectDollarParamReportedOnlyOn(
      f, {12, 17, 19, 21, 23, 25, 27, 30, 32, 34, 36, 39, 43},
      {15, 18, 20, 22, 24, 26, 28, 31, 33, 35, 37, 40, 45});
}

TEST(
    DollarConstantElaboration,
    DollarParameterStandsAloneOnlyAsARangesUpperBoundAValueRangesBoundOrAnActual) {
  ElabFixture f;
  Elaborate(
      "checker ck(x, n);\n"
      "endchecker\n"
      "module top;\n"
      "  parameter P = $;\n"
      "  bit clk, a, b, c, d;\n"
      "  int n;\n"
      "  logic x;\n"
      "  sequence s(e, m);\n"
      "    e ##[1:m] e;\n"
      "  endsequence\n"
      "  property pf(P);\n"
      "    @(posedge clk) a ##1 (b == P);\n"
      "  endproperty\n"
      "  property inq1(r1, r2);\n"
      "    @(posedge clk) a ##[r1:r2] b ##1 c |=> d;\n"
      "  endproperty\n"
      "  property pd(e, m = P);\n"
      "    @(posedge clk) e ##[1:m] e;\n"
      "  endproperty\n"
      "  property pe(e, m = P - 1);\n"
      "    @(posedge clk) e ##[1:m] e;\n"
      "  endproperty\n"
      "  initial begin\n"
      "    if (n inside {[0:P]}) x = 1;\n"
      "    if (n inside {[P:5]}) x = 1;\n"
      "    if (n inside {[0:P - 1]}) x = 1;\n"
      "  end\n"
      "  assert property (inq1(3, P));\n"
      "  assert property (inq1(3, P - 1));\n"
      "  assert property (@(posedge clk) s(a, P));\n"
      "  ck k1(a, P);\n"
      "  ck k2(a, P + 1);\n"
      "  assert property (@(posedge clk) a ##[1:P] b);\n"
      "  assert property (@(posedge clk) a ##[1:P - 1] b);\n"
      "  assert property (@(posedge clk) a ##[P:3] b);\n"
      "  assert property (@(posedge clk) a ##P b);\n"
      "  assert property (@(posedge clk) a[*1:P] ##1 b[->1:P] ##1 a[=0:P]);\n"
      "  assert property (@(posedge clk) a[*1:P + 1] ##1 b);\n"
      "  assert property (@(posedge clk) a[*P] ##1 b);\n"
      "  assert property (@(posedge clk) a[*P:3] ##1 b);\n"
      "  assert property (@(posedge clk) always [1:P] a);\n"
      "  assert property (@(posedge clk) s_eventually [2:P] a);\n"
      "  assert property (@(posedge clk) always [1:P - 1] a);\n"
      "  assert property (@(posedge clk) always [P:3] a);\n"
      "endmodule\n",
      f);
  ExpectDollarParamReportedOnlyOn(
      f, {20, 26, 29, 32, 34, 35, 36, 38, 39, 40, 43, 44},
      {12, 17, 24, 25, 28, 30, 31, 33, 37, 41, 42});
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "", 41, "16.12.11"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "", 42, "16.12.13"));
}

TEST(DollarConstantElaboration,
     DollarParameterUseThatAGuardLeavesUnevaluatedIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module top;\n"
      "  parameter P = $;\n"
      "  parameter Q = 4;\n"
      "  logic [7:0] w1, w2, w3, w4, w5, x;\n"
      "  if (!$isunbounded(P) && (P == 0)) begin : g1\n"
      "  end\n"
      "  if ($isunbounded(P) && (P == 0)) begin : g2\n"
      "  end\n"
      "  if ($isunbounded(P)) begin : g3\n"
      "    assign w1 = P;\n"
      "  end else begin : g4\n"
      "    assign w2 = P;\n"
      "  end\n"
      "  if (!$isunbounded(P)) begin : g5\n"
      "    assign w3 = P;\n"
      "  end\n"
      "  assign w4 = $isunbounded(P) || P == 0;\n"
      "  assign w5 = !$isunbounded(P) || P == 0;\n"
      "  initial begin\n"
      "    if (!$isunbounded(P) && (P == 0)) x = 1;\n"
      "    x = $isunbounded(P) ? 0 : P;\n"
      "    x = $isunbounded(P) ? P : 0;\n"
      "    if ($isunbounded(P))\n"
      "      x = P;\n"
      "    else\n"
      "      x = P;\n"
      "    if ($isunbounded(Q))\n"
      "      x = Q;\n"
      "    else\n"
      "      x = Q;\n"
      "  end\n"
      "endmodule\n",
      f);
  ExpectDollarParamReportedOnlyOn(f, {7, 10, 18, 22, 24},
                                  {5, 12, 15, 17, 20, 21, 26, 28, 30});
}

TEST(DollarConstantElaboration,
     DollarParameterIsJudgedInEveryDesignElementGenerateBlockAndSubroutine) {
  ElabFixture f;
  Elaborate(
      "parameter U = $;\n"
      "interface quiet_if #(parameter int lo = 0, parameter int hi = 0)\n"
      "    (input logic clk, input logic [1:0] en);\n"
      "  if (!$isunbounded(hi) && (hi == 0)) begin : never\n"
      "    assert property (@(posedge clk) en != 0);\n"
      "  end else begin : window\n"
      "    assert property (@(posedge clk) (en == 0)[*lo:hi] ##1 en != 0);\n"
      "  end\n"
      "  if (hi == 1) begin : unguarded\n"
      "  end\n"
      "endinterface\n"
      "program prg #(parameter P = $)(input logic clk, input logic e);\n"
      "  int x;\n"
      "  initial x = P;\n"
      "  initial if (!$isunbounded(P) && P > 2) x = 1;\n"
      "  assert property (@(posedge clk) e[*1:P] ##1 !e);\n"
      "endprogram\n"
      "checker chk(logic clk, logic e);\n"
      "  assert property (@(posedge clk) e[*1:U] ##1 !e);\n"
      "  assert property (@(posedge clk) e ##1 (e == U));\n"
      "endchecker\n"
      "module sub #(parameter N = 1, parameter M = $)(input logic clk);\n"
      "  logic [7:0] y1, y2;\n"
      "  assign y1 = N;\n"
      "  assign y2 = M;\n"
      "endmodule\n"
      "module top;\n"
      "  parameter P = $;\n"
      "  bit clk, a, b, e;\n"
      "  logic [1:0] en;\n"
      "  logic [7:0] x;\n"
      "  quiet_if #(0, 0) q0(clk, en);\n"
      "  quiet_if #(0, $) q1(clk, en);\n"
      "  prg p1(clk, e);\n"
      "  chk c1(clk, e);\n"
      "  sub #(.N($), .M(4)) s1(clk);\n"
      "  if (1) begin : g\n"
      "    localparam G = $;\n"
      "    logic [7:0] y;\n"
      "    assign y = G;\n"
      "    assert property (@(posedge clk) a[*1:G] ##1 b);\n"
      "  end\n"
      "  task t;\n"
      "    x = P;\n"
      "  endtask\n"
      "  function int h(int P);\n"
      "    return P;\n"
      "  endfunction\n"
      "  function int k();\n"
      "    int P;\n"
      "    P = 2;\n"
      "    return P;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ExpectDollarParamReportedOnlyOn(f, {9, 14, 20, 24, 40, 44},
                                  {4, 7, 15, 16, 19, 25, 41, 47, 52});
}

TEST(DollarConstantElaboration,
     DollarParameterIsJudgedInAPackageAClassAndTheCompilationUnit) {
  ElabFixture f;
  Elaborate(
      "package pk;\n"
      "  parameter P = $;\n"
      "  parameter Q = 4;\n"
      "  function int f();\n"
      "    return P;\n"
      "  endfunction\n"
      "  function int g();\n"
      "    return Q;\n"
      "  endfunction\n"
      "endpackage\n"
      "parameter U = $;\n"
      "function int uf();\n"
      "  return U;\n"
      "endfunction\n"
      "class C #(parameter K = $);\n"
      "  parameter L = $;\n"
      "  rand int v;\n"
      "  constraint c1 { v inside {[0:K]}; }\n"
      "  constraint c2 { v inside {[0:L - 1]}; }\n"
      "  function int m();\n"
      "    return K;\n"
      "  endfunction\n"
      "endclass\n"
      "module top;\n"
      "  import pk::*;\n"
      "  logic [7:0] y1, y2, y3, y4, y5;\n"
      "  int n;\n"
      "  logic x;\n"
      "  assign y1 = pk::P;\n"
      "  assign y2 = pk::Q;\n"
      "  assign y3 = $unit::U;\n"
      "  assign y4 = U;\n"
      "  assign y5 = P;\n"
      "  initial if (n inside {[0:pk::P]}) x = 1;\n"
      "endmodule\n",
      f);
  ExpectDollarParamReportedOnlyOn(f, {5, 13, 19, 21, 29, 31, 32, 33},
                                  {8, 18, 30, 34});
}

TEST(DollarConstantElaboration,
     DollarParameterInACovergroupStandsOnlyAsAValueRangesBoundOrAMatchesCount) {
  ElabFixture f;
  Elaborate(
      "package pk;\n"
      "  parameter P = $;\n"
      "  bit [3:0] pv;\n"
      "  covergroup pcg;\n"
      "    coverpoint pv {\n"
      "      bins a = {P};\n"
      "      bins b = {[2:P]};\n"
      "    }\n"
      "  endgroup\n"
      "endpackage\n"
      "parameter U = $;\n"
      "bit [3:0] uv;\n"
      "covergroup ucg;\n"
      "  coverpoint uv {\n"
      "    bins a = {U};\n"
      "    bins b = {[U:5]};\n"
      "  }\n"
      "endgroup\n"
      "class C #(parameter K = $);\n"
      "  bit [3:0] cv;\n"
      "  covergroup ccg;\n"
      "    coverpoint cv {\n"
      "      bins a = {K};\n"
      "      bins b = {[2:K]};\n"
      "    }\n"
      "  endgroup\n"
      "  function new;\n"
      "    ccg = new;\n"
      "  endfunction\n"
      "endclass\n"
      "interface ifc #(parameter H = 1)(input bit clk);\n"
      "  bit [3:0] iv;\n"
      "  covergroup icg @(posedge clk);\n"
      "    coverpoint iv {\n"
      "      bins a = {H};\n"
      "      bins b = {[2:H]};\n"
      "    }\n"
      "  endgroup\n"
      "endinterface\n"
      "module top;\n"
      "  parameter P = $;\n"
      "  parameter Q = 4;\n"
      "  bit clk;\n"
      "  bit [3:0] a, b;\n"
      "  ifc #($) i1(clk);\n"
      "  covergroup cg @(posedge clk);\n"
      "    cpa: coverpoint a {\n"
      "      bins v1 = {[0:P]};\n"
      "      bins v2 = {[P:5]};\n"
      "      bins v3 = {P};\n"
      "      bins v4 = {[0:P - 1]};\n"
      "      bins v5[P] = {[0:3]};\n"
      "      bins v6[] = {[0:3]} with (item < P);\n"
      "      bins v7 = {1} iff (P);\n"
      "      bins v8 = (1 => [0:P]);\n"
      "      bins v9 = (1 [*2:P] => 2);\n"
      "      bins v10 = {Q};\n"
      "      option.weight = P;\n"
      "    }\n"
      "    cpb: coverpoint b iff (P == 1);\n"
      "    bit [P:0] cpc: coverpoint a;\n"
      "    x: cross cpa, cpb {\n"
      "      bins s1 = binsof(cpa) intersect {[0:P]};\n"
      "      bins s2 = binsof(cpa) intersect {P};\n"
      "      bins s3 = binsof(cpa) with (cpa > P);\n"
      "      bins s4 = binsof(cpa) with (cpa > 1) matches P;\n"
      "      bins s5 = binsof(cpa) with (cpa > 1) matches P - 1;\n"
      "    }\n"
      "  endgroup\n"
      "  covergroup cg2(int P) @(posedge clk);\n"
      "    coverpoint a {\n"
      "      bins h = {P};\n"
      "    }\n"
      "  endgroup\n"
      "  if (1) begin : g\n"
      "    localparam G = $;\n"
      "    covergroup gcg @(posedge clk);\n"
      "      coverpoint a {\n"
      "        bins g1 = {G};\n"
      "        bins g2 = {[1:G]};\n"
      "      }\n"
      "    endgroup\n"
      "  end\n"
      "endmodule\n",
      f);
  ExpectDollarParamReportedOnlyOn(
      f, {6, 15, 23, 35, 50, 51, 52, 53, 54, 56, 58, 60, 61, 64, 65, 67, 79},
      {7, 16, 24, 36, 48, 49, 55, 57, 63, 66, 72, 80});
}

TEST(DollarConstantElaboration, DollarParameterIsAParametersValueOnlyAlone) {
  ElabFixture f;
  Elaborate(
      "parameter U = $;\n"
      "parameter UV = U + 1;\n"
      "parameter UW = U;\n"
      "package pk;\n"
      "  parameter P = $;\n"
      "  parameter R = P + 1;\n"
      "  parameter S = P;\n"
      "endpackage\n"
      "class C #(parameter K = $,\n"
      "          parameter L = K + 1,\n"
      "          parameter M = K);\n"
      "  parameter N = K - 1;\n"
      "  parameter O = K;\n"
      "endclass\n"
      "class D extends C #(U - 1);\n"
      "endclass\n"
      "class E extends C #(U);\n"
      "endclass\n"
      "module sub #(parameter A = $,\n"
      "             parameter B = A + 1,\n"
      "             parameter N = 1)();\n"
      "endmodule\n"
      "module sub2 #(parameter A = $,\n"
      "              parameter B = A + 1)();\n"
      "endmodule\n"
      "module top;\n"
      "  parameter P = $;\n"
      "  parameter Q = 4;\n"
      "  parameter R = P + 1;\n"
      "  localparam S = P;\n"
      "  localparam T = Q + 1;\n"
      "  localparam V = $isunbounded(P) ? 0 : P + 1;\n"
      "  sub #(.N(P + 1)) s1();\n"
      "  sub #(.N(P)) s2();\n"
      "  sub #(P - 1) s3();\n"
      "  sub2 #(.B(3)) s4();\n"
      "  C #(P - 1) c1;\n"
      "  C #(P) c2;\n"
      "  C #(.K(P + 1)) c3;\n"
      "  C #(.K(Q + 1)) c4;\n"
      "  if (1) begin : g\n"
      "    localparam G = $;\n"
      "    localparam H = G * 2;\n"
      "    localparam I = G;\n"
      "  end\n"
      "endmodule\n",
      f);
  ExpectDollarParamReportedOnlyOn(
      f, {2, 6, 10, 12, 15, 20, 29, 33, 35, 37, 39, 43},
      {3, 7, 11, 13, 17, 24, 30, 31, 32, 34, 38, 40, 44});
}

}  // namespace
