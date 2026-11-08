#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string_view>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

struct Expected {
  std::string_view var;
  uint64_t value;
};

void ExpectValues(SimFixture& f, std::initializer_list<Expected> expected) {
  for (const Expected& e : expected) {
    const Variable* v = f.ctx.FindVariable(e.var);
    EXPECT_NE(v, nullptr) << e.var;
    if (v != nullptr) EXPECT_EQ(v->value.ToUint64(), e.value) << e.var;
  }
}

TEST(AggregateParameterConstantReads, MembersFoldForEachInstancesValue) {
  SimFixture f;
  RunAndFindVar(
      "typedef struct { int a; logic [7:0] b; } s_t;\n"
      "module m #(parameter s_t P = '{a: 5, b: 8'h3});\n"
      "  localparam int Q = 11;\n"
      "  localparam int W = P.a;\n"
      "  logic [P.b-1:0] v;\n"
      "  logic [W-1:0] u;\n"
      "  int n, k, br;\n"
      "  if (P.a == 5) begin : g\n"
      "    initial br = 1;\n"
      "  end else begin : g\n"
      "    initial br = 2;\n"
      "  end\n"
      "  initial begin\n"
      "    n = $bits(v);\n"
      "    k = $bits(u);\n"
      "  end\n"
      "endmodule\n"
      "module t;\n"
      "  localparam s_t L = '{b: 8'h6, a: 7};\n"
      "  parameter int Q = 3;\n"
      "  m d();\n"
      "  m #(.P('{b: 8'h2, a: 9})) x();\n"
      "  m #('{4, 8'h5}) y();\n"
      "  m #(s_t'{b: 8'h7, a: 5}) z();\n"
      "  m #(.P(L)) w();\n"
      "  m r();\n"
      "  defparam r.P = '{a: 6, b: 8'h4};\n"
      "  m #(.P('{a: Q, b: 8'h1})) o();\n"
      "endmodule\n",
      f, "d.n");
  EXPECT_FALSE(f.has_errors);
  ExpectValues(
      f,
      {{"d.n", 3}, {"d.k", 5}, {"d.br", 1}, {"x.n", 2}, {"x.k", 9}, {"x.br", 2},
       {"y.n", 5}, {"y.k", 4}, {"y.br", 2}, {"z.n", 7}, {"z.k", 5}, {"z.br", 1},
       {"w.n", 6}, {"w.k", 7}, {"w.br", 2}, {"r.n", 4}, {"r.k", 6}, {"r.br", 2},
       {"o.n", 1}, {"o.k", 3}, {"o.br", 2}});
}

TEST(AggregateParameterConstantReads, ElementsFoldForEachShapeAndValue) {
  SimFixture f;
  RunAndFindVar(
      "typedef int pair_t [2];\n"
      "module s #(parameter int A[2] = '{3, 4},\n"
      "           parameter int D[1:0] = '{5, 6},\n"
      "           parameter int U[0:1] = '{7, 8});\n"
      "  localparam int W = A[1];\n"
      "  logic [A[0]-1:0] v;\n"
      "  logic [W-1:0] u;\n"
      "  logic [D[1]-1:0] e;\n"
      "  logic [U[1]-1:0] c;\n"
      "  int n, k, m, j, br;\n"
      "  if (D[0] == 6) begin : g\n"
      "    initial br = 1;\n"
      "  end else begin : g\n"
      "    initial br = 2;\n"
      "  end\n"
      "  initial begin\n"
      "    n = $bits(v);\n"
      "    k = $bits(u);\n"
      "    m = $bits(e);\n"
      "    j = $bits(c);\n"
      "  end\n"
      "endmodule\n"
      "module t;\n"
      "  localparam int B[2] = '{9, 10};\n"
      "  s d();\n"
      "  s #(.A('{1: 6, 0: 2}), .D('{0: 9, 1: 2}), .U('{1: 3, 0: 4})) x();\n"
      "  s #(.A('{default: 5}), .D('{0: 6, default: 3})) y();\n"
      "  s #(.A('{2{7}})) r();\n"
      "  s #(.A(pair_t'{8, 11}), .D(B), .U(B)) z();\n"
      "endmodule\n",
      f, "d.n");
  EXPECT_FALSE(f.has_errors);
  ExpectValues(f,
               {{"d.n", 3},  {"d.k", 4}, {"d.m", 5},  {"d.j", 8},  {"d.br", 1},
                {"x.n", 2},  {"x.k", 6}, {"x.m", 2},  {"x.j", 3},  {"x.br", 2},
                {"y.n", 5},  {"y.k", 5}, {"y.m", 3},  {"y.j", 8},  {"y.br", 1},
                {"r.n", 7},  {"r.k", 7}, {"r.m", 5},  {"r.br", 1}, {"z.n", 8},
                {"z.k", 11}, {"z.m", 9}, {"z.j", 10}, {"z.br", 2}});
}

TEST(AggregateParameterConstantReads, DeeperSelectsFold) {
  SimFixture f;
  RunAndFindVar(
      "typedef struct { int x; logic [3:0] y; } in_t;\n"
      "typedef struct {\n"
      "  int arr [2];\n"
      "  in_t in;\n"
      "  logic [7:0] b;\n"
      "  logic [0:7] c;\n"
      "} o_t;\n"
      "typedef struct { int a; logic [7:0] b; } s_t;\n"
      "module t;\n"
      "  parameter int M [2][2] = '{'{1, 2}, '{3, 4}};\n"
      "  parameter s_t S [2] = '{'{a: 5, b: 8'h6}, '{b: 8'h8, a: 7}};\n"
      "  parameter o_t P =\n"
      "      '{arr: '{9, 10}, in: '{x: 11, y: 4'h3}, b: 8'hA5, c: 8'h80};\n"
      "  parameter logic [7:0] E [2] = '{8'h12, 8'h34};\n"
      "  localparam int L = M[1][0] + S[1].a + P.arr[1] + P.in.x;\n"
      "  logic [L-1:0] l;\n"
      "  logic [M[1][0]-1:0] m10;\n"
      "  logic [S[1].a-1:0] s1a;\n"
      "  logic [P.arr[1]-1:0] parr;\n"
      "  logic [P.in.x-1:0] pinx;\n"
      "  logic [P.b[3:0]-1:0] pb;\n"
      "  logic [P.b[7]+1:0] pb7;\n"
      "  logic [E[1][7:4]-1:0] e1;\n"
      "  logic [P.c[0]+1:0] pc0;\n"
      "  logic [P.c[0:3]-1:0] pc;\n"
      "  int nl, nm, ns, na, nx, nb, nb7, ne, nc0, nc, br;\n"
      "  if (P.in.y == 3 && E[0][3:0] == 2) begin : g\n"
      "    initial br = 1;\n"
      "  end else begin : g\n"
      "    initial br = 2;\n"
      "  end\n"
      "  initial begin\n"
      "    nl = $bits(l);\n"
      "    nm = $bits(m10);\n"
      "    ns = $bits(s1a);\n"
      "    na = $bits(parr);\n"
      "    nx = $bits(pinx);\n"
      "    nb = $bits(pb);\n"
      "    nb7 = $bits(pb7);\n"
      "    ne = $bits(e1);\n"
      "    nc0 = $bits(pc0);\n"
      "    nc = $bits(pc);\n"
      "  end\n"
      "endmodule\n",
      f, "nl");
  EXPECT_FALSE(f.has_errors);
  ExpectValues(f, {{"nl", 31},
                   {"nm", 3},
                   {"ns", 7},
                   {"na", 10},
                   {"nx", 11},
                   {"nb", 5},
                   {"nb7", 3},
                   {"ne", 3},
                   {"nc0", 3},
                   {"nc", 8},
                   {"br", 1}});
}

TEST(AggregateParameterConstantReads, ReadsFoldInAnInterfaceProgramAndBlock) {
  SimFixture f;
  RunAndFindVar(
      "typedef struct { int a; logic [7:0] b; } s_t;\n"
      "interface ifc #(parameter s_t P = '{a: 3, b: 8'h4});\n"
      "  localparam int W = P.a;\n"
      "  logic [P.b-1:0] v;\n"
      "  logic [W-1:0] u;\n"
      "  int n, k, br;\n"
      "  if (P.a == 3) begin : g\n"
      "    initial br = 1;\n"
      "  end else begin : g\n"
      "    initial br = 2;\n"
      "  end\n"
      "  initial begin\n"
      "    n = $bits(v);\n"
      "    k = $bits(u);\n"
      "  end\n"
      "endinterface\n"
      "program prg #(parameter int A[2] = '{2, 6});\n"
      "  localparam int W = A[1];\n"
      "  logic [A[0]-1:0] v;\n"
      "  logic [W-1:0] u;\n"
      "  int n, k;\n"
      "  initial begin\n"
      "    n = $bits(v);\n"
      "    k = $bits(u);\n"
      "  end\n"
      "endprogram\n"
      "module t;\n"
      "  ifc #(.P('{b: 8'h5, a: 9})) i();\n"
      "  prg #(.A('{1: 4, 0: 7})) p();\n"
      "  int n, k, br;\n"
      "  if (1) begin : g\n"
      "    localparam s_t G = '{b: 8'h5, a: 6};\n"
      "    localparam int A[2] = '{2, 9};\n"
      "    localparam int W = G.a + A[1];\n"
      "    logic [G.b-1:0] v;\n"
      "    logic [W-1:0] u;\n"
      "    if (G.a == 6) begin : h\n"
      "      initial br = 1;\n"
      "    end\n"
      "    initial begin\n"
      "      n = $bits(v);\n"
      "      k = $bits(u);\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "n");
  EXPECT_FALSE(f.has_errors);
  ExpectValues(f, {{"i.n", 5},
                   {"i.k", 9},
                   {"i.br", 2},
                   {"p.n", 7},
                   {"p.k", 4},
                   {"n", 5},
                   {"k", 15},
                   {"br", 1}});
}

TEST(AggregateParameterConstantReads, ReadsFoldFromAPackageTheUnitAndAClass) {
  SimFixture f;
  RunAndFindVar(
      "typedef struct { int a; logic [7:0] b; } s_t;\n"
      "parameter s_t U = '{b: 8'h2, a: 6};\n"
      "localparam int UW = U.a;\n"
      "package pk;\n"
      "  typedef struct { int a; logic [7:0] b; } k_t;\n"
      "  parameter k_t K = '{b: 8'h3, a: 12};\n"
      "  parameter int A[2] = '{4, 5};\n"
      "  localparam int W = K.a + A[1];\n"
      "endpackage\n"
      "class C;\n"
      "  localparam s_t K = '{b: 8'h7, a: 9};\n"
      "  localparam int A[2] = '{2, 5};\n"
      "  localparam int W = K.a + A[1];\n"
      "endclass\n"
      "module t;\n"
      "  logic [pk::K.b-1:0] pv;\n"
      "  logic [pk::A[1]-1:0] pa;\n"
      "  logic [pk::W-1:0] pw;\n"
      "  logic [U.b-1:0] uv;\n"
      "  logic [UW-1:0] uw;\n"
      "  logic [$unit::U.a-1:0] ua;\n"
      "  logic [C::K.b-1:0] cv;\n"
      "  logic [C::W-1:0] cw;\n"
      "  int npv, npa, npw, nuv, nuw, nua, ncv, ncw, br;\n"
      "  if (pk::K.a == 12 && C::K.a == 9) begin : g\n"
      "    initial br = 1;\n"
      "  end else begin : g\n"
      "    initial br = 2;\n"
      "  end\n"
      "  initial begin\n"
      "    npv = $bits(pv);\n"
      "    npa = $bits(pa);\n"
      "    npw = $bits(pw);\n"
      "    nuv = $bits(uv);\n"
      "    nuw = $bits(uw);\n"
      "    nua = $bits(ua);\n"
      "    ncv = $bits(cv);\n"
      "    ncw = $bits(cw);\n"
      "  end\n"
      "endmodule\n",
      f, "npv");
  EXPECT_FALSE(f.has_errors);
  ExpectValues(f, {{"npv", 3},
                   {"npa", 5},
                   {"npw", 17},
                   {"nuv", 2},
                   {"nuw", 6},
                   {"nua", 6},
                   {"ncv", 7},
                   {"ncw", 14},
                   {"br", 1}});
}

TEST(AggregateParameterConstantReads, ReadsFoldInAFunctionAndANamedBlock) {
  SimFixture f;
  RunAndFindVar(
      "typedef struct { int a; logic [7:0] b; } s_t;\n"
      "module t;\n"
      "  function automatic int f();\n"
      "    localparam s_t K = '{b: 8'h5, a: 3};\n"
      "    localparam int A[2] = '{2, 6};\n"
      "    localparam int W = K.a + A[1];\n"
      "    logic [K.b-1:0] v;\n"
      "    logic [W-1:0] u;\n"
      "    return $bits(v) * 100 + $bits(u);\n"
      "  endfunction\n"
      "  int nf, nb;\n"
      "  initial begin : nb_blk\n"
      "    localparam s_t K = '{b: 8'h4, a: 7};\n"
      "    localparam int A[2] = '{1, 8};\n"
      "    localparam int W = K.a + A[1];\n"
      "    logic [K.b-1:0] v;\n"
      "    logic [W-1:0] u;\n"
      "    nf = f();\n"
      "    nb = $bits(v) * 100 + $bits(u);\n"
      "  end\n"
      "endmodule\n",
      f, "nf");
  EXPECT_FALSE(f.has_errors);
  ExpectValues(f, {{"nf", 509}, {"nb", 415}});
}

}  // namespace
