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

TEST(AggregateParameterConstantReads, TypeAndDefaultKeysReachNestedParts) {
  SimFixture f;
  RunAndFindVar(
      "typedef struct { int x; logic [3:0] y; } in_t;\n"
      "typedef struct { int arr [2]; in_t in; byte b; } o_t;\n"
      "module t;\n"
      "  parameter o_t P = '{int: 7, default: 3};\n"
      "  parameter o_t Q = '{in: '{x: 2, default: 5}, default: 4};\n"
      "  parameter o_t R = '{int: 6, int: 9, byte: 2, default: 1};\n"
      "  parameter o_t D = '{default: 2};\n"
      "  parameter int G [2][2] = '{default: 3};\n"
      "  parameter int H [2][2] = '{int: 6};\n"
      "  parameter int K [3] = '{1: 5, byte: 2, default: 8};\n"
      "  parameter byte KB [3] = '{1: 5, byte: 2, default: 8};\n"
      "  logic [P.arr[1]-1:0] v1;\n"
      "  logic [P.in.x-1:0] v2;\n"
      "  logic [P.in.y-1:0] v3;\n"
      "  logic [P.b-1:0] v4;\n"
      "  logic [Q.in.x-1:0] v5;\n"
      "  logic [Q.in.y-1:0] v6;\n"
      "  logic [Q.arr[0]-1:0] v7;\n"
      "  logic [Q.b-1:0] v8;\n"
      "  logic [R.in.x-1:0] v9;\n"
      "  logic [R.in.y-1:0] v10;\n"
      "  logic [R.b-1:0] v11;\n"
      "  logic [D.in.x-1:0] v12;\n"
      "  logic [D.arr[1]-1:0] v13;\n"
      "  logic [G[1][0]-1:0] v14;\n"
      "  logic [H[0][1]-1:0] v15;\n"
      "  logic [K[1]-1:0] v16;\n"
      "  logic [K[0]-1:0] v17;\n"
      "  logic [KB[0]-1:0] v18;\n"
      "  logic [KB[1]-1:0] v19;\n"
      "  int n1, n2, n3, n4, n5, n6, n7, n8, n9, n10;\n"
      "  int n11, n12, n13, n14, n15, n16, n17, n18, n19;\n"
      "  initial begin\n"
      "    n1 = $bits(v1);\n"
      "    n2 = $bits(v2);\n"
      "    n3 = $bits(v3);\n"
      "    n4 = $bits(v4);\n"
      "    n5 = $bits(v5);\n"
      "    n6 = $bits(v6);\n"
      "    n7 = $bits(v7);\n"
      "    n8 = $bits(v8);\n"
      "    n9 = $bits(v9);\n"
      "    n10 = $bits(v10);\n"
      "    n11 = $bits(v11);\n"
      "    n12 = $bits(v12);\n"
      "    n13 = $bits(v13);\n"
      "    n14 = $bits(v14);\n"
      "    n15 = $bits(v15);\n"
      "    n16 = $bits(v16);\n"
      "    n17 = $bits(v17);\n"
      "    n18 = $bits(v18);\n"
      "    n19 = $bits(v19);\n"
      "  end\n"
      "endmodule\n",
      f, "n1");
  EXPECT_FALSE(f.has_errors);
  ExpectValues(f, {{"n1", 7},
                   {"n2", 7},
                   {"n3", 3},
                   {"n4", 3},
                   {"n5", 2},
                   {"n6", 5},
                   {"n7", 4},
                   {"n8", 4},
                   {"n9", 9},
                   {"n10", 1},
                   {"n11", 2},
                   {"n12", 2},
                   {"n13", 2},
                   {"n14", 3},
                   {"n15", 6},
                   {"n16", 5},
                   {"n17", 8},
                   {"n18", 2},
                   {"n19", 5}});
}

TEST(AggregateParameterConstantReads,
     DefaultNamingAWholeValueFillsAggregateParts) {
  SimFixture f;
  RunAndFindVar(
      "typedef struct { int x; logic [3:0] y; } in_t;\n"
      "typedef struct { in_t p; in_t q; int k; } two_t;\n"
      "typedef int row_t [2];\n"
      "module t;\n"
      "  parameter in_t I = '{x: 12, y: 4'h6};\n"
      "  parameter two_t T = '{k: 1, default: I};\n"
      "  parameter two_t U = '{k: 2, default: in_t'{5, 4'h2}};\n"
      "  parameter int ROW [2] = '{5, 6};\n"
      "  parameter int G [2][2] = '{default: ROW};\n"
      "  parameter int F [2][2] = '{default: row_t'{7, 8}};\n"
      "  parameter int C [2] = '{int'(3), 4};\n"
      "  parameter int SEED [2] = '{3, 21};\n"
      "  parameter two_t V = '{k: 2, default: SEED[1]};\n"
      "  logic [T.q.x-1:0] v1;\n"
      "  logic [T.p.y-1:0] v2;\n"
      "  logic [T.k-1:0] v3;\n"
      "  logic [U.q.x-1:0] v4;\n"
      "  logic [U.p.y-1:0] v5;\n"
      "  logic [G[1][0]-1:0] v6;\n"
      "  logic [G[0][1]-1:0] v7;\n"
      "  logic [F[1][1]-1:0] v8;\n"
      "  logic [F[0][0]-1:0] v9;\n"
      "  logic [C[0]-1:0] v10;\n"
      "  logic [V.q.x-1:0] v11;\n"
      "  logic [V.p.y-1:0] v12;\n"
      "  logic [V.k-1:0] v13;\n"
      "  int n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13;\n"
      "  initial begin\n"
      "    n1 = $bits(v1);\n"
      "    n2 = $bits(v2);\n"
      "    n3 = $bits(v3);\n"
      "    n4 = $bits(v4);\n"
      "    n5 = $bits(v5);\n"
      "    n6 = $bits(v6);\n"
      "    n7 = $bits(v7);\n"
      "    n8 = $bits(v8);\n"
      "    n9 = $bits(v9);\n"
      "    n10 = $bits(v10);\n"
      "    n11 = $bits(v11);\n"
      "    n12 = $bits(v12);\n"
      "    n13 = $bits(v13);\n"
      "  end\n"
      "endmodule\n",
      f, "n1");
  EXPECT_FALSE(f.has_errors);
  ExpectValues(f, {{"n1", 12},
                   {"n2", 6},
                   {"n3", 1},
                   {"n4", 5},
                   {"n5", 2},
                   {"n6", 5},
                   {"n7", 6},
                   {"n8", 8},
                   {"n9", 7},
                   {"n10", 3},
                   {"n11", 21},
                   {"n12", 5},
                   {"n13", 2}});
}

TEST(AggregateParameterConstantReads, PackedPartsFoldFromPatternsAndIntegers) {
  SimFixture f;
  RunAndFindVar(
      "typedef struct packed { logic [3:0] hi; logic [3:0] lo; } ps_t;\n"
      "typedef struct packed { logic signed [3:0] hi; logic [3:0] lo; }\n"
      "    sg_t;\n"
      "typedef union packed { logic [7:0] a; logic [7:0] b; } u_t;\n"
      "typedef logic [3:0] nib_t;\n"
      "typedef logic [0:3] rev_t;\n"
      "typedef struct {\n"
      "  ps_t p;\n"
      "  logic [1:0][3:0] q;\n"
      "  int k;\n"
      "  nib_t n;\n"
      "  sg_t s;\n"
      "  ps_t [1:0] pa;\n"
      "  rev_t r;\n"
      "  ps_t [0:1] pb;\n"
      "} w_t;\n"
      "module t;\n"
      "  parameter w_t W = '{p: '{lo: 4'h3, hi: 4'h1}, q: '{4'h1, 4'h2},\n"
      "                      k: 2, n: 4'h9, s: 8'hF2,\n"
      "                      pa: '{1: 8'h12, 0: 8'h34}, r: 4'h8,\n"
      "                      pb: '{1: 8'h12, 0: 8'h34}};\n"
      "  parameter w_t X = '{p: 8'h25, q: 8'h34, k: 1, n: 4'h1, s: 8'h12,\n"
      "                      pa: 16'h0, r: 4'h0, pb: 16'h0};\n"
      "  parameter w_t Y = '{default: 4'h1};\n"
      "  parameter w_t Z = '{nib_t: 9, default: 0};\n"
      "  parameter ps_t PS = '{lo: 4'h7, hi: 4'h2};\n"
      "  parameter u_t U = 8'h2A;\n"
      "  logic [W.p-1:0] v1;\n"
      "  logic [W.p.lo-1:0] v2;\n"
      "  logic [W.p.hi-1:0] v3;\n"
      "  logic [W.q-1:0] v4;\n"
      "  logic [W.r[3]:0] v5;\n"
      "  logic [X.p.lo-1:0] v6;\n"
      "  logic [X.p.hi-1:0] v7;\n"
      "  logic [X.q-1:0] v8;\n"
      "  logic [Y.p-1:0] v9;\n"
      "  logic [Y.q-1:0] v10;\n"
      "  logic [Y.k-1:0] v11;\n"
      "  logic [Y.n-1:0] v12;\n"
      "  logic [Z.p-1:0] v13;\n"
      "  logic [Z.q-1:0] v14;\n"
      "  logic [Z.n-1:0] v15;\n"
      "  logic [Z.k:0] v16;\n"
      "  logic [PS.lo-1:0] v17;\n"
      "  logic [PS.hi-1:0] v18;\n"
      "  logic [U.b-1:0] v19;\n"
      "  int n1, n2, n3, n4, n5, n6, n7, n8, n9, n10;\n"
      "  int n11, n12, n13, n14, n15, n16, n17, n18, n19, br;\n"
      "  if (W.s.hi < 0 && X.s.hi > 0 && W.pa == 16'h1234 &&\n"
      "      Y.pa == 16'h1111 && Z.r == 0 && W.pb == 16'h3412) begin : g\n"
      "    initial br = 1;\n"
      "  end else begin : g\n"
      "    initial br = 2;\n"
      "  end\n"
      "  initial begin\n"
      "    n1 = $bits(v1);\n"
      "    n2 = $bits(v2);\n"
      "    n3 = $bits(v3);\n"
      "    n4 = $bits(v4);\n"
      "    n5 = $bits(v5);\n"
      "    n6 = $bits(v6);\n"
      "    n7 = $bits(v7);\n"
      "    n8 = $bits(v8);\n"
      "    n9 = $bits(v9);\n"
      "    n10 = $bits(v10);\n"
      "    n11 = $bits(v11);\n"
      "    n12 = $bits(v12);\n"
      "    n13 = $bits(v13);\n"
      "    n14 = $bits(v14);\n"
      "    n15 = $bits(v15);\n"
      "    n16 = $bits(v16);\n"
      "    n17 = $bits(v17);\n"
      "    n18 = $bits(v18);\n"
      "    n19 = $bits(v19);\n"
      "  end\n"
      "endmodule\n",
      f, "n1");
  EXPECT_FALSE(f.has_errors);
  ExpectValues(f,
               {{"n1", 19}, {"n2", 3},  {"n3", 1},    {"n4", 18},   {"n5", 1},
                {"n6", 5},  {"n7", 2},  {"n8", 52},   {"n9", 17},   {"n10", 17},
                {"n11", 1}, {"n12", 1}, {"n13", 153}, {"n14", 153}, {"n15", 9},
                {"n16", 1}, {"n17", 7}, {"n18", 2},   {"n19", 42},  {"br", 1}});
}

TEST(AggregateParameterConstantReads, TypeKeysMatchMembersOfAnEquivalentType) {
  SimFixture f;
  RunAndFindVar(
      "typedef struct {\n"
      "  logic [7:0] a;\n"
      "  bit b;\n"
      "  bit signed [31:0] c;\n"
      "  string s;\n"
      "} sa;\n"
      "module t;\n"
      "  parameter sa S1 = '{int: 1, default: 0, string: \"\"};\n"
      "  parameter sa S2 = '{int: 5, default: 2, string: \"abc\"};\n"
      "  parameter sa S3 = '{a: 8'h1, b: 1, s: \"x\", int: 4};\n"
      "  logic [S1.c:0] v1;\n"
      "  logic [S1.a:0] v2;\n"
      "  logic [S1.s.len():0] v3;\n"
      "  logic [S2.c-1:0] v4;\n"
      "  logic [S2.a-1:0] v5;\n"
      "  logic [S2.b:0] v6;\n"
      "  logic [S2.s.len()-1:0] v7;\n"
      "  logic [S3.c-1:0] v8;\n"
      "  logic [S3.s.len():0] v9;\n"
      "  int n1, n2, n3, n4, n5, n6, n7, n8, n9;\n"
      "  initial begin\n"
      "    n1 = $bits(v1);\n"
      "    n2 = $bits(v2);\n"
      "    n3 = $bits(v3);\n"
      "    n4 = $bits(v4);\n"
      "    n5 = $bits(v5);\n"
      "    n6 = $bits(v6);\n"
      "    n7 = $bits(v7);\n"
      "    n8 = $bits(v8);\n"
      "    n9 = $bits(v9);\n"
      "  end\n"
      "endmodule\n",
      f, "n1");
  EXPECT_FALSE(f.has_errors);
  ExpectValues(f, {{"n1", 2},
                   {"n2", 1},
                   {"n3", 1},
                   {"n4", 5},
                   {"n5", 2},
                   {"n6", 1},
                   {"n7", 3},
                   {"n8", 4},
                   {"n9", 2}});
}

TEST(AggregateParameterConstantReads, RealAndStringPartsFold) {
  SimFixture f;
  RunAndFindVar(
      "typedef struct { real r; shortreal sr; int i; string s; } rs_t;\n"
      "module t;\n"
      "  parameter rs_t P = '{r: 2.6, sr: 0.1, i: 2.6, s: \"hey\"};\n"
      "  parameter real RA [2] = '{1.5, 3.25};\n"
      "  parameter string SA [2] = '{\"ab\", \"wxyz\"};\n"
      "  localparam int RI = P.r;\n"
      "  localparam RR = P.r * 2;\n"
      "  localparam real RE = RA[1] * 4;\n"
      "  localparam real RK = P.i / 2.0;\n"
      "  localparam string S = P.s;\n"
      "  localparam string T = SA[0];\n"
      "  parameter logic [3:0] W4 = 4'b0110;\n"
      "  localparam real RW = W4[1] * 1.5;\n"
      "  logic [RI-1:0] v1;\n"
      "  logic [$rtoi(RR)-1:0] v2;\n"
      "  logic [$rtoi(RE)-1:0] v3;\n"
      "  logic [$rtoi(RK * 4)-1:0] v4;\n"
      "  logic [P.i-1:0] v5;\n"
      "  logic [$rtoi((P.sr - 0.1) * 1.0e9) + 1:0] v6;\n"
      "  logic [S.len()-1:0] v7;\n"
      "  logic [P.s.len()-1:0] v8;\n"
      "  logic [SA[1].len()-1:0] v9;\n"
      "  logic [P.s.getc(1) - 100:0] v10;\n"
      "  logic [P.i[1] * 4 + P.i[2] * 2:0] v11;\n"
      "  logic [T.len()-1:0] v12;\n"
      "  logic [$rtoi(RW * 2)-1:0] v13;\n"
      "  int n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, br;\n"
      "  if (P.s == \"hey\") begin : g\n"
      "    initial br = 1;\n"
      "  end else begin : g\n"
      "    initial br = 2;\n"
      "  end\n"
      "  initial begin\n"
      "    n1 = $bits(v1);\n"
      "    n2 = $bits(v2);\n"
      "    n3 = $bits(v3);\n"
      "    n4 = $bits(v4);\n"
      "    n5 = $bits(v5);\n"
      "    n6 = $bits(v6);\n"
      "    n7 = $bits(v7);\n"
      "    n8 = $bits(v8);\n"
      "    n9 = $bits(v9);\n"
      "    n10 = $bits(v10);\n"
      "    n11 = $bits(v11);\n"
      "    n12 = $bits(v12);\n"
      "    n13 = $bits(v13);\n"
      "  end\n"
      "endmodule\n",
      f, "n1");
  EXPECT_FALSE(f.has_errors);
  ExpectValues(f, {{"n1", 3},
                   {"n2", 5},
                   {"n3", 13},
                   {"n4", 6},
                   {"n5", 3},
                   {"n6", 3},
                   {"n7", 3},
                   {"n8", 3},
                   {"n9", 4},
                   {"n10", 2},
                   {"n11", 5},
                   {"n12", 2},
                   {"n13", 3},
                   {"br", 1}});
}

TEST(AggregateParameterConstantReads,
     AliasesTypeParametersAndImplicitTypesFold) {
  SimFixture f;
  RunAndFindVar(
      "typedef struct { int x; logic [3:0] y; } in_t;\n"
      "typedef struct { int arr [2]; in_t in; } o_t;\n"
      "module t;\n"
      "  parameter int M [2][2] = '{'{1, 2}, '{3, 4}};\n"
      "  parameter int R [2] = M[1];\n"
      "  parameter o_t O = '{arr: '{9, 10}, in: '{x: 11, y: 4'h3}};\n"
      "  parameter in_t I = O.in;\n"
      "  parameter int D [0:1] = '{1: 5, 0: 6};\n"
      "  parameter int A [1:0] = D;\n"
      "  parameter N [2] = '{3, 4};\n"
      "  parameter signed S [2] = '{-2, 5};\n"
      "  parameter [3:0] Q [2] = '{20, 3};\n"
      "  logic [R[0]-1:0] v1;\n"
      "  logic [I.x-1:0] v2;\n"
      "  logic [A[1]-1:0] v3;\n"
      "  logic [A[0]-1:0] v4;\n"
      "  logic [N[1]-1:0] v5;\n"
      "  logic [Q[0]-1:0] v6;\n"
      "  logic [S[1]-1:0] v7;\n"
      "  int n1, n2, n3, n4, n5, n6, n7, br;\n"
      "  if (S[0] < 0) begin : g\n"
      "    initial br = 1;\n"
      "  end else begin : g\n"
      "    initial br = 2;\n"
      "  end\n"
      "  initial begin\n"
      "    n1 = $bits(v1);\n"
      "    n2 = $bits(v2);\n"
      "    n3 = $bits(v3);\n"
      "    n4 = $bits(v4);\n"
      "    n5 = $bits(v5);\n"
      "    n6 = $bits(v6);\n"
      "    n7 = $bits(v7);\n"
      "  end\n"
      "endmodule\n",
      f, "n1");
  EXPECT_FALSE(f.has_errors);
  ExpectValues(f, {{"n1", 3},
                   {"n2", 11},
                   {"n3", 6},
                   {"n4", 5},
                   {"n5", 4},
                   {"n6", 4},
                   {"n7", 5},
                   {"br", 1}});
}

TEST(AggregateParameterConstantReads, ValuesTypedByATypeParameterFold) {
  SimFixture f;
  RunAndFindVar(
      "typedef struct { int a; logic [7:0] b; } s_t;\n"
      "typedef struct { logic [3:0] z; int a; } z_t;\n"
      "module m #(type T = s_t, parameter T P = '{a: 3, b: 8'h4});\n"
      "  logic [P.a-1:0] v;\n"
      "  int n;\n"
      "  initial n = $bits(v);\n"
      "endmodule\n"
      "module t;\n"
      "  m d();\n"
      "  m #(.T(z_t), .P('{4'h1, 7})) o();\n"
      "endmodule\n",
      f, "d.n");
  EXPECT_FALSE(f.has_errors);
  ExpectValues(f, {{"d.n", 3}, {"o.n", 7}});
}

TEST(AggregateParameterConstantReads, ElementMembersSizeProceduralRanges) {
  SimFixture f;
  RunAndFindVar(
      "typedef struct { int a; logic [7:0] b; } s_t;\n"
      "module t;\n"
      "  int n;\n"
      "  initial begin : b\n"
      "    localparam s_t S [2] = '{'{a: 3, b: 8'h1}, '{a: 6, b: 8'h2}};\n"
      "    logic [S[1].a-1:0] v;\n"
      "    logic [0:S[0].a-1] w;\n"
      "    n = $bits(v) * 100 + $bits(w);\n"
      "  end\n"
      "endmodule\n",
      f, "n");
  EXPECT_FALSE(f.has_errors);
  ExpectValues(f, {{"n", 603}});
}

}  // namespace
