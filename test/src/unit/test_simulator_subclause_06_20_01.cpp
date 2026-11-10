#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ParameterArraySim, PositionalPatternFillsTheElements) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter int A[4] = '{1, 2, 3, 4};\n"
                       "  initial $display(\"%0d %0d\", A[1], A[3]);\n"
                       "endmodule\n",
                       f),
            "2 4\n");
}

TEST(ParameterArraySim, DescendingDimensionTakesItemsFromTheLeft) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  localparam int D[3:0] = '{1, 2, 3, 4};\n"
                       "  initial $display(\"%0d %0d\", D[3], D[0]);\n"
                       "endmodule\n",
                       f),
            "1 4\n");
}

TEST(ParameterArraySim, NestedPatternFillsTwoDimensions) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter int M[2][2] = '{'{1, 2}, '{3, 4}};\n"
                       "  initial $display(\"%0d %0d\", M[0][1], M[1][0]);\n"
                       "endmodule\n",
                       f),
            "2 3\n");
}

TEST(ParameterArraySim, DefaultKeyFillsEveryElement) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter int K[3] = '{default: 7};\n"
                       "  initial $display(\"%0d %0d\", K[0], K[2]);\n"
                       "endmodule\n",
                       f),
            "7 7\n");
}

TEST(ParameterArraySim, RealElementsKeepTheirFractions) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter real R[2] = '{1.5, 0.25};\n"
                       "  initial $display(\"%g %g\", R[0], R[1]);\n"
                       "endmodule\n",
                       f),
            "1.5 0.25\n");
}

TEST(ParameterArraySim, ParameterPortArrayFillsTheElements) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t #(parameter int A[2] = '{1, 2});\n"
                       "  initial $display(\"%0d %0d\", A[0], A[1]);\n"
                       "endmodule\n",
                       f),
            "1 2\n");
}

TEST(ParameterArraySim, ClauseExampleReadsAPartSelectOfAnElement) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter logic [31:0] P1 [3:0] = '{1, 2, 3, 4};\n"
                       "  initial begin\n"
                       "    if (P1[2][7:0])\n"
                       "      $display(\"%0d %0d\", P1[2][7:0], P1[0][7:0]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "2 4\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(ParameterArraySim, PartSelectOfAnElementTakesThatElementsBits) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  parameter logic [31:0] P1 [3:0] =\n"
                 "      '{32'h1, 32'h2A3B, 32'h3, 32'h4};\n"
                 "  initial $display(\"%h %h\", P1[2][7:0], P1[2][15:8]);\n"
                 "endmodule\n",
                 f),
      "3b 2a\n");
  EXPECT_FALSE(f.has_errors);
}

uint64_t ValueOf(SimFixture& f, std::string_view name) {
  const Variable* v = f.ctx.FindVariable(name);
  EXPECT_NE(v, nullptr) << name;
  return v == nullptr ? ~uint64_t{0} : v->value.ToUint64();
}

TEST(ParameterArraySim, WholeArrayDefparamGivesEveryElement) {
  SimFixture f;
  RunAndFindVar(
      "module sub;\n"
      "  parameter int A[2] = '{1, 2};\n"
      "  int x, y;\n"
      "  initial begin\n"
      "    x = A[0];\n"
      "    y = A[1];\n"
      "  end\n"
      "endmodule\n"
      "module t;\n"
      "  sub u();\n"
      "  sub d();\n"
      "  defparam u.A = '{5, 6};\n"
      "endmodule\n",
      f, "u.x");
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ValueOf(f, "u.x"), 5u);
  EXPECT_EQ(ValueOf(f, "u.y"), 6u);
  EXPECT_EQ(ValueOf(f, "d.x"), 1u);
  EXPECT_EQ(ValueOf(f, "d.y"), 2u);
}

TEST(StructureParameterSim, MembersReadTheDefaultOrTheWholeOverride) {
  SimFixture f;
  RunAndFindVar(
      "typedef struct { int a; logic [7:0] b; } s_t;\n"
      "module m #(parameter s_t P = '{a: 1, b: 8'h2});\n"
      "  int a;\n"
      "  logic [7:0] b;\n"
      "  initial begin\n"
      "    a = P.a;\n"
      "    b = P.b;\n"
      "  end\n"
      "endmodule\n"
      "module t;\n"
      "  m d();\n"
      "  m #(.P('{b: 8'h6, a: 5})) u();\n"
      "  m #('{a: 7, b: 8'h8}) v();\n"
      "endmodule\n",
      f, "d.a");
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ValueOf(f, "d.a"), 1u);
  EXPECT_EQ(ValueOf(f, "d.b"), 2u);
  EXPECT_EQ(ValueOf(f, "u.a"), 5u);
  EXPECT_EQ(ValueOf(f, "u.b"), 6u);
  EXPECT_EQ(ValueOf(f, "v.a"), 7u);
  EXPECT_EQ(ValueOf(f, "v.b"), 8u);
}

TEST(StructureParameterSim, BodyParameterAndLocalparamMembersAreRead) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef struct { int a; logic [7:0] b; } s_t;\n"
                       "module t;\n"
                       "  parameter s_t Q = '{a: 3, b: 8'h4};\n"
                       "  localparam s_t L = '{b: 8'h9, a: 10};\n"
                       "  parameter s_t R = Q;\n"
                       "  initial $display(\"%0d %0d %0d %0d %0d %0d\", Q.a, "
                       "Q.b, L.a, L.b, R.a, R.b);\n"
                       "endmodule\n",
                       f),
            "3 4 10 9 3 4\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(StructureParameterSim, WholeStructureDefparamGivesEveryMember) {
  SimFixture f;
  RunAndFindVar(
      "typedef struct { int a; logic [7:0] b; } s_t;\n"
      "module sub;\n"
      "  parameter s_t P = '{a: 1, b: 8'h2};\n"
      "  int a;\n"
      "  logic [7:0] b;\n"
      "  initial begin\n"
      "    a = P.a;\n"
      "    b = P.b;\n"
      "  end\n"
      "endmodule\n"
      "module t;\n"
      "  sub u();\n"
      "  sub d();\n"
      "  defparam u.P = '{b: 8'h3, a: 9};\n"
      "endmodule\n",
      f, "u.a");
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ValueOf(f, "u.a"), 9u);
  EXPECT_EQ(ValueOf(f, "u.b"), 3u);
  EXPECT_EQ(ValueOf(f, "d.a"), 1u);
  EXPECT_EQ(ValueOf(f, "d.b"), 2u);
}

TEST(StructureParameterSim, DefaultNamingAParameterOrATypedPatternIsWhole) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("typedef struct { int a; logic [7:0] b; } s_t;\n"
                 "typedef int pair_t [2];\n"
                 "module t;\n"
                 "  localparam s_t L = '{b: 8'h9, a: 10};\n"
                 "  parameter s_t R = L;\n"
                 "  parameter s_t T = s_t'{b: 8'h6, a: 5};\n"
                 "  parameter int B[2] = '{7, 8};\n"
                 "  parameter int C[2] = B;\n"
                 "  parameter int D[2] = pair_t'{3, 4};\n"
                 "  initial $display(\"%0d %0d %0d %0d %0d %0d %0d %0d\", "
                 "R.a, R.b, T.a, T.b, C[0], C[1], D[0], D[1]);\n"
                 "endmodule\n",
                 f),
      "10 9 5 6 7 8 3 4\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(StructureParameterSim, OverrideByANameOrATypedPatternGivesEveryMember) {
  SimFixture f;
  RunAndFindVar(
      "typedef struct { int a; logic [7:0] b; } s_t;\n"
      "module m #(parameter s_t P = '{a: 1, b: 8'h2});\n"
      "  int a;\n"
      "  logic [7:0] b;\n"
      "  initial begin\n"
      "    a = P.a;\n"
      "    b = P.b;\n"
      "  end\n"
      "endmodule\n"
      "module t;\n"
      "  localparam s_t L = '{b: 8'h9, a: 10};\n"
      "  parameter s_t Q = '{b: 8'h4, a: 3};\n"
      "  m #(.P(L)) w();\n"
      "  m #(s_t'{b: 8'h7, a: 8}) x();\n"
      "  m y();\n"
      "  m z();\n"
      "  defparam y.P = Q;\n"
      "  defparam z.P = s_t'{b: 8'h5, a: 11};\n"
      "endmodule\n",
      f, "w.a");
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ValueOf(f, "w.a"), 10u);
  EXPECT_EQ(ValueOf(f, "w.b"), 9u);
  EXPECT_EQ(ValueOf(f, "x.a"), 8u);
  EXPECT_EQ(ValueOf(f, "x.b"), 7u);
  EXPECT_EQ(ValueOf(f, "y.a"), 3u);
  EXPECT_EQ(ValueOf(f, "y.b"), 4u);
  EXPECT_EQ(ValueOf(f, "z.a"), 11u);
  EXPECT_EQ(ValueOf(f, "z.b"), 5u);
}

TEST(ParameterArraySim, OverrideByANameOrATypedPatternGivesEveryElement) {
  SimFixture f;
  RunAndFindVar(
      "typedef int pair_t [2];\n"
      "module sub;\n"
      "  parameter int A[2] = '{1, 2};\n"
      "  int e0, e1;\n"
      "  initial begin\n"
      "    e0 = A[0];\n"
      "    e1 = A[1];\n"
      "  end\n"
      "endmodule\n"
      "module t;\n"
      "  localparam int B[2] = '{7, 8};\n"
      "  parameter int C[2] = '{3, 4};\n"
      "  sub #(.A(B)) w();\n"
      "  sub #(pair_t'{5, 6}) x();\n"
      "  sub y();\n"
      "  sub z();\n"
      "  defparam y.A = C;\n"
      "  defparam z.A = pair_t'{9, 10};\n"
      "endmodule\n",
      f, "w.e0");
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ValueOf(f, "w.e0"), 7u);
  EXPECT_EQ(ValueOf(f, "w.e1"), 8u);
  EXPECT_EQ(ValueOf(f, "x.e0"), 5u);
  EXPECT_EQ(ValueOf(f, "x.e1"), 6u);
  EXPECT_EQ(ValueOf(f, "y.e0"), 3u);
  EXPECT_EQ(ValueOf(f, "y.e1"), 4u);
  EXPECT_EQ(ValueOf(f, "z.e0"), 9u);
  EXPECT_EQ(ValueOf(f, "z.e1"), 10u);
}

constexpr std::string_view kWholeDefparamTarget =
    "typedef struct { int a; logic [7:0] b; } s_t;\n"
    "module m;\n"
    "  parameter int W = 100;\n"
    "  parameter s_t Q = '{a: 200, b: 8'h20};\n"
    "  parameter int C[2] = '{300, 400};\n"
    "  parameter s_t P = '{a: 1, b: 8'h2};\n"
    "  parameter s_t R = '{a: 1, b: 8'h2};\n"
    "  parameter int A[2] = '{1, 2};\n"
    "  parameter int B[2] = '{1, 2};\n"
    "  int pa, pb, ra, rb, a0, a1, b0, b1;\n"
    "  initial begin\n"
    "    pa = P.a;\n"
    "    pb = P.b;\n"
    "    ra = R.a;\n"
    "    rb = R.b;\n"
    "    a0 = A[0];\n"
    "    a1 = A[1];\n"
    "    b0 = B[0];\n"
    "    b1 = B[1];\n"
    "  end\n"
    "endmodule\n";

TEST(StructureParameterSim, WholeDefparamFromAFartherModuleNamesTheWriters) {
  SimFixture f;
  std::string src(kWholeDefparamTarget);
  src +=
      "module mid;\n"
      "  parameter int W = 50;\n"
      "  parameter s_t Q = '{a: 60, b: 8'h6};\n"
      "  parameter int C[2] = '{70, 80};\n"
      "  m u();\n"
      "  m v();\n"
      "endmodule\n"
      "module w;\n"
      "  parameter int W = 30;\n"
      "  parameter s_t Q = '{a: 31, b: 8'h32};\n"
      "  parameter int C[2] = '{33, 34};\n"
      "  defparam top.t.v.P = '{a: W, b: 8'h3};\n"
      "  defparam top.t.v.A = '{W, 4};\n"
      "  defparam top.t.v.R = Q;\n"
      "  defparam top.t.v.B = C;\n"
      "endmodule\n"
      "module top;\n"
      "  parameter int W = 7;\n"
      "  parameter s_t Q = '{a: 8, b: 8'h9};\n"
      "  parameter int C[2] = '{11, 12};\n"
      "  mid t();\n"
      "  w x();\n"
      "  defparam t.u.P = '{a: W, b: 8'h1};\n"
      "  defparam t.u.A = '{W, 2};\n"
      "  defparam t.u.R = Q;\n"
      "  defparam t.u.B = C;\n"
      "  initial begin\n"
      "    #1;\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d %0d %0d\", t.u.pa, t.u.pb, "
      "t.u.ra, t.u.rb, t.u.a0, t.u.a1, t.u.b0, t.u.b1);\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d %0d %0d\", t.v.pa, t.v.pb, "
      "t.v.ra, t.v.rb, t.v.a0, t.v.a1, t.v.b0, t.v.b1);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunCapture(src, f), "7 1 8 9 7 2 11 12\n30 3 31 50 30 4 33 34\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(StructureParameterSim, WholeDefparamInAGenerateBlockNamesTheBlocks) {
  SimFixture f;
  std::string src(kWholeDefparamTarget);
  src +=
      "module top;\n"
      "  parameter int W = 7;\n"
      "  parameter s_t Q = '{a: 8, b: 8'h9};\n"
      "  if (1) begin : g\n"
      "    localparam int W = 40;\n"
      "    localparam s_t Q = '{a: 41, b: 8'h2a};\n"
      "    m k();\n"
      "    defparam k.P = '{a: W, b: 8'h1};\n"
      "    defparam k.A = '{W, 2};\n"
      "    defparam k.R = Q;\n"
      "  end\n"
      "  for (genvar i = 0; i < 2; i++) begin : l\n"
      "    m k();\n"
      "    defparam k.P = '{a: i + 20, b: 8'h1};\n"
      "    defparam k.A = '{W, i};\n"
      "    defparam k.R = Q;\n"
      "  end\n"
      "  initial begin\n"
      "    #1;\n"
      "    $display(\"%0d %0d %0d %0d %0d\", g.k.pa, g.k.a0, g.k.a1, "
      "g.k.ra, g.k.rb);\n"
      "    $display(\"%0d %0d %0d %0d %0d\", l[0].k.pa, l[0].k.a0, "
      "l[0].k.a1, l[0].k.ra, l[0].k.rb);\n"
      "    $display(\"%0d %0d %0d %0d %0d\", l[1].k.pa, l[1].k.a0, "
      "l[1].k.a1, l[1].k.ra, l[1].k.rb);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunCapture(src, f), "40 40 2 41 42\n20 7 0 8 9\n21 7 1 8 9\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(StructureParameterSim, MemberOfAnElementOfAStructureArrayIsRead) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef struct { int a; logic [7:0] b; } s_t;\n"
                       "module t;\n"
                       "  parameter s_t S [2] =\n"
                       "      '{'{b: 8'h2, a: 1}, '{b: 8'h4, a: 3}};\n"
                       "  initial $display(\"%0d %0d\", S[1].a, S[0].b);\n"
                       "endmodule\n",
                       f),
            "3 2\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(StructureParameterSim, MembersAreReadInAGenerateBlock) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef struct { int a; logic [7:0] b; } s_t;\n"
                       "module t;\n"
                       "  if (1) begin : g\n"
                       "    localparam s_t G = '{b: 8'h18, a: 17};\n"
                       "    localparam int A[2] = '{19, 20};\n"
                       "    initial $display(\"%0d %0d %0d\", G.a, G.b, "
                       "A[1]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "17 24 20\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(StructureParameterSim, MembersAreReadFromAPackageAndTheUnit) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef struct { int a; logic [7:0] b; } s_t;\n"
                       "parameter s_t U = '{a: 11, b: 8'h12};\n"
                       "package pk;\n"
                       "  parameter s_t K = '{b: 8'h14, a: 13};\n"
                       "  parameter int A[2] = '{15, 16};\n"
                       "endpackage\n"
                       "module t;\n"
                       "  initial $display(\"%0d %0d %0d %0d %0d\", U.a, U.b, "
                       "pk::K.a, pk::K.b, pk::A[1]);\n"
                       "endmodule\n",
                       f),
            "11 18 13 20 16\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(StructureParameterSim, MembersAreReadInAClass) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef struct { int a; logic [7:0] b; } s_t;\n"
                       "class C;\n"
                       "  localparam s_t K = '{b: 8'h1A, a: 19};\n"
                       "  localparam int A[2] = '{21, 22};\n"
                       "  static function int f();\n"
                       "    return K.a + A[1];\n"
                       "  endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  initial $display(\"%0d %0d\", C::f(), C::K.b);\n"
                       "endmodule\n",
                       f),
            "41 26\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(StructureParameterSim, MembersAreReadInAnInterface) {
  SimFixture f;
  RunAndFindVar(
      "typedef struct { int a; logic [7:0] b; } s_t;\n"
      "interface ifc #(parameter s_t P = '{a: 1, b: 8'h2});\n"
      "  int a;\n"
      "  initial a = P.a + P.b;\n"
      "endinterface\n"
      "module t;\n"
      "  ifc #(.P('{b: 8'h5, a: 30})) i();\n"
      "  ifc d();\n"
      "endmodule\n",
      f, "i.a");
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ValueOf(f, "i.a"), 35u);
  EXPECT_EQ(ValueOf(f, "d.a"), 3u);
}

TEST(StructureParameterSim, MembersAreReadInAProgramAFunctionAndANamedBlock) {
  SimFixture f;
  RunAndFindVar(
      "typedef struct { int a; logic [7:0] b; } s_t;\n"
      "program prg #(parameter s_t P = '{b: 8'h3, a: 2});\n"
      "  parameter int A[2] = '{4, 5};\n"
      "  int r;\n"
      "  initial r = P.a * 100 + P.b * 10 + A[1];\n"
      "endprogram\n"
      "module t;\n"
      "  function automatic int f();\n"
      "    localparam s_t K = '{b: 8'h6, a: 7};\n"
      "    localparam int B[2] = '{8, 9};\n"
      "    return K.a * 100 + K.b * 10 + B[0];\n"
      "  endfunction\n"
      "  prg #(.P('{a: 1, b: 8'h2})) p();\n"
      "  int nf, nb;\n"
      "  initial begin : blk\n"
      "    localparam s_t K = '{a: 4, b: 8'h1};\n"
      "    localparam int A[2] = '{3, 6};\n"
      "    nf = f();\n"
      "    nb = K.a * 100 + K.b * 10 + A[1];\n"
      "  end\n"
      "endmodule\n",
      f, "nf");
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ValueOf(f, "p.r"), 125u);
  EXPECT_EQ(ValueOf(f, "nf"), 768u);
  EXPECT_EQ(ValueOf(f, "nb"), 416u);
}

TEST(InPlaceTypeParameterSim, ModuleParametersOfInPlaceTypesReadBack) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module n #(enum bit {N0, N1} P = N1,\n"
          "           struct packed {bit [3:0] a;} Q = 4'h1);\n"
          "endmodule\n"
          "module t #(parameter enum {A, B} P = B,\n"
          "           struct packed {logic [3:0] a;} Q = 4'b1x0z,\n"
          "           localparam union packed {bit [3:0] x; bit [3:0] y;} "
          "L = 4'b1x0z);\n"
          "  parameter enum logic [1:0] {C, D, E} G = E, H = C;\n"
          "  localparam struct packed {bit [3:0] a;} S = 4'b1x0z;\n"
          "  parameter struct {int a; logic [3:0] b;} R = '{1, 4'bz01x};\n"
          "  localparam union packed {logic [3:0] u; logic [3:0] w;} "
          "U = 4'bz01x;\n"
          "  parameter int K = D + B;\n"
          "  n #(.Q(4'h7)) u();\n"
          "  initial $display(\"%0d %b %b %b %b %b %0d %b %b %0d %0d %b %b "
          "%b\", P, Q, L, G, H, S, R.a, R.b, U, K, A, Q.a, u.P, u.Q);\n"
          "endmodule\n",
          f),
      "1 1x0z 1000 10 00 1000 1 z01x z01x 2 0 1x0z 1 0111\n");
}

TEST(InPlaceTypeParameterSim, InterfaceAndGenerateParametersReadBack) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "interface ifc #(struct packed {logic [3:0] a;} IP = 4'b1x0z);\n"
          "  parameter enum {I0, I1, I2} IE = I2;\n"
          "  localparam union packed {bit [3:0] a; bit [3:0] b;} "
          "IU = 4'b1x0z;\n"
          "endinterface\n"
          "module t;\n"
          "  ifc i();\n"
          "  if (1) begin : g\n"
          "    parameter enum logic [1:0] {G0, G1, G2} GE = G2;\n"
          "    localparam struct packed {bit [3:0] a;} GS = 4'b1x0z;\n"
          "    parameter int GK = G1;\n"
          "  end\n"
          "  initial $display(\"%b %0d %b %b %b %0d\", i.IP, i.IE, i.IU, "
          "g.GE, g.GS, g.GK);\n"
          "endmodule\n",
          f),
      "1x0z 2 1000 10 1000 1\n");
}

TEST(InPlaceTypeParameterSim, ProgramParametersOfInPlaceTypesReadBack) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("program prg #(parameter enum {P0, P1} PE = P1);\n"
                 "  localparam struct packed {logic [3:0] a;} PS = 4'bz01x;\n"
                 "  parameter union packed {bit [3:0] a; bit [3:0] b;} "
                 "PU = 4'bz01x;\n"
                 "  initial $display(\"%0d %b %b %0d\", PE, PS, PU, P0);\n"
                 "endprogram\n"
                 "module t;\n"
                 "  prg u();\n"
                 "endmodule\n",
                 f),
      "1 z01x 0010 0\n");
}

TEST(InPlaceTypeParameterSim, PackageAndUnitParametersReadBack) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "parameter enum {UA, UB, UC} UE = UC;\n"
          "localparam struct packed {logic [3:0] a;} US = 4'b1x0z;\n"
          "parameter int UK = UB + 2;\n"
          "package pk;\n"
          "  parameter enum logic [2:0] {KA = 3, KB = 5} KE = KB;\n"
          "  localparam union packed {bit [3:0] a; bit [3:0] b;} "
          "KU = 4'b1x0z;\n"
          "  parameter struct {int a; logic [3:0] b;} KR = "
          "'{a: 6, b: 4'b1z0x};\n"
          "  parameter int KI = KA;\n"
          "endpackage\n"
          "module t;\n"
          "  initial $display(\"%0d %b %0d %0d %b %0d %b %0d %0d\", UE, US, "
          "UK, pk::KE, pk::KU, pk::KR.a, pk::KR.b, pk::KI, UB);\n"
          "endmodule\n",
          f),
      "2 1x0z 3 5 1000 6 1z0x 3 1\n");
}

TEST(InPlaceTypeParameterSim, ClassParametersOfInPlaceTypesReadBack) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "class C #(struct packed {bit [3:0] a;} P = 4'b1x0z,\n"
          "          parameter union packed {logic [3:0] x; logic [3:0] y;} "
          "Q = 4'b1x0z,\n"
          "          parameter union soft {logic [3:0] m; logic [3:0] n;} "
          "W = 4'bz10x);\n"
          "  localparam struct packed {logic [3:0] a;} S = 4'bz01x;\n"
          "endclass\n"
          "class D;\n"
          "  parameter struct {int a; int b;} R = '{a: 4, b: 9};\n"
          "  localparam union packed {bit [3:0] u; bit [3:0] w;} "
          "U = 4'b1x0z;\n"
          "  localparam union soft {logic [3:0] s; logic [3:0] t;} "
          "V = 4'b01xz;\n"
          "endclass\n"
          "module t;\n"
          "  initial $display(\"%b %b %b %b %0d %0d %b %b %b\", C#()::P, "
          "C#()::Q, C#()::S, C#(4'h6)::P, D::R.a, D::R.b, D::U, C#()::W, "
          "D::V);\n"
          "endmodule\n",
          f),
      "1000 1x0z z01x 0110 4 9 1000 z10x 01xz\n");
}

TEST(InPlaceTypeParameterSim, SubroutineAndBlockParametersReadBack) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  int r;\n"
                 "  function automatic int f();\n"
                 "    parameter enum {FA, FB, FC} FE = FC;\n"
                 "    localparam struct packed {bit [3:0] a;} FS = 4'b1x0z;\n"
                 "    return FE * 100 + FS;\n"
                 "  endfunction\n"
                 "  function int g();\n"
                 "    parameter enum {GA, GB} GE = GB;\n"
                 "    return GE + 10;\n"
                 "  endfunction\n"
                 "  task automatic tk(output int o);\n"
                 "    parameter struct {int a; int b;} TR = '{a: 3, b: 4};\n"
                 "    parameter enum {TA, TB, TC} TE = TB;\n"
                 "    o = TR.a + TR.b + TE * 10;\n"
                 "  endtask\n"
                 "  initial begin : b\n"
                 "    parameter enum logic [1:0] {BA, BB} BE = BB;\n"
                 "    localparam union packed {logic [3:0] a; logic [3:0] b;} "
                 "BU = 4'b1x0z;\n"
                 "    tk(r);\n"
                 "    $display(\"%0d %0d %0d %b %b %0d\", f(), g(), r, BE, BU, "
                 "BA);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "208 11 17 01 1x0z 0\n");
}

TEST(ParameterDeclarationSim,
     ImplicitTypeWithTwoPackedDimensionsInAModuleAndItsPortList) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m #(parameter [1:0][3:0] MP = 8'h12,\n"
                       "           localparam [1:0][3:0] ML = 8'h34);\n"
                       "  parameter [1:0][3:0] P = 8'hA5;\n"
                       "  parameter signed [1:0][3:0] Q = 8'hA5;\n"
                       "  parameter unsigned [1:0][3:0] R = 8'hA5, S = 8'h5A;\n"
                       "  localparam [1:0][3:0] L = 8'hA5;\n"
                       "  initial begin\n"
                       "    $display(\"%0d %h %h\", $bits(MP), MP[1], MP[0]);\n"
                       "    $display(\"%0d %h\", $bits(ML), ML[1]);\n"
                       "    $display(\"%0d %h %h\", $bits(P), P[1], P[0]);\n"
                       "    $display(\"%0d %0d %h\", $bits(Q), Q, Q[1]);\n"
                       "    $display(\"%0d %0d %h\", $bits(R), R, S[1]);\n"
                       "    $display(\"%h\", L[0]);\n"
                       "  end\n"
                       "endmodule\n"
                       "module t;\n"
                       "  m #(.MP(8'hF0)) u ();\n"
                       "endmodule\n",
                       f),
            "8 f 0\n8 3\n8 a 5\n8 -91 a\n8 165 5\n5\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(ParameterDeclarationSim,
     ImplicitTypeWithTwoPackedDimensionsInEveryOtherScope) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package pk;\n"
                 "  parameter [1:0][3:0] PK = 8'hC3;\n"
                 "endpackage\n"
                 "localparam [1:0][3:0] U = 8'h96;\n"
                 "interface ifc #(parameter [1:0][3:0] IP = 8'h21);\n"
                 "  parameter [1:0][3:0] I = 8'h5A;\n"
                 "endinterface\n"
                 "program pg #(localparam [1:0][3:0] GP = 8'h43);\n"
                 "  parameter [1:0][3:0] G = 8'h69;\n"
                 "  initial #2 $display(\"%0d %h %0d %h\", $bits(G), G[1], "
                 "$bits(GP), GP[0]);\n"
                 "endprogram\n"
                 "class C #(parameter [1:0][3:0] CP = 8'h3C);\n"
                 "  parameter [1:0][3:0] CB = 8'hE1;\n"
                 "  static function void show();\n"
                 "    $display(\"%0d %h %0d %h\", $bits(CP), CP[1], $bits(CB), "
                 "CB[0]);\n"
                 "  endfunction\n"
                 "endclass\n"
                 "module t;\n"
                 "  ifc ii ();\n"
                 "  pg pp ();\n"
                 "  if (1) begin : g\n"
                 "    parameter [1:0][3:0] GB = 8'h7E;\n"
                 "  end\n"
                 "  function automatic int fn();\n"
                 "    parameter [1:0][3:0] FP = 8'hD2;\n"
                 "    return $bits(FP) * 100 + FP[1];\n"
                 "  endfunction\n"
                 "  initial begin : b\n"
                 "    parameter [1:0][3:0] BP = 8'hB4;\n"
                 "    $display(\"%0d %h\", $bits(pk::PK), pk::PK[1]);\n"
                 "    $display(\"%0d %h\", $bits(U), U[1]);\n"
                 "    $display(\"%0d %h %0d %h\", $bits(ii.I), ii.I[1], "
                 "$bits(ii.IP), ii.IP[1]);\n"
                 "    C#()::show();\n"
                 "    C#(8'h0F)::show();\n"
                 "    $display(\"%0d %h\", $bits(g.GB), g.GB[1]);\n"
                 "    $display(\"%0d %h %0d\", $bits(BP), BP[0], fn());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "8 c\n8 9\n8 5 8 2\n8 3 8 1\n8 0 8 1\n8 7\n8 4 813\n8 6 8 3\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(ClassParameterWithoutDefaultSim,
     ClauseExampleSizesItsArrayFromTheTypedef) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class Mem #(type T, int size);\n"
                       "  T words[size];\n"
                       "endclass\n"
                       "typedef Mem#(byte, 1024) Kbyte;\n"
                       "module t;\n"
                       "  Kbyte k;\n"
                       "  initial begin\n"
                       "    k = new;\n"
                       "    k.words[1023] = 8'h5A;\n"
                       "    $display(\"%0d %0d %h\", $size(k.words), "
                       "$bits(k.words[0]), k.words[1023]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1024 8 5a\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(ClassParameterWithoutDefaultSim,
     OrderedAndNamedSpecializationsEachSizeTheirOwnArray) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class Mem #(type T, int size);\n"
                       "  T words[size];\n"
                       "endclass\n"
                       "module t;\n"
                       "  Mem#(shortint, 6) a;\n"
                       "  Mem#(.size(3), .T(int)) b;\n"
                       "  initial begin\n"
                       "    a = new;\n"
                       "    b = new;\n"
                       "    a.words[5] = 16'hBEEF;\n"
                       "    b.words[2] = 32'h12345678;\n"
                       "    $display(\"%0d %0d %h\", $size(a.words), "
                       "$bits(a.words[0]), a.words[5]);\n"
                       "    $display(\"%0d %0d %h\", $size(b.words), "
                       "$bits(b.words[0]), b.words[2]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "6 16 beef\n3 32 12345678\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(ClassParameterWithoutDefaultSim, RangesAndTwoDimensionsTakeTheValue) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class Mem #(type T, int size);\n"
                       "  T up[0:size-1];\n"
                       "  T down[size+1:2];\n"
                       "  T grid[size][2];\n"
                       "endclass\n"
                       "module t;\n"
                       "  Mem#(shortint, 6) k;\n"
                       "  initial begin\n"
                       "    k = new;\n"
                       "    k.up[5] = 16'h0AAA;\n"
                       "    k.down[7] = 16'h0BBB;\n"
                       "    k.grid[5][1] = 16'h0CCC;\n"
                       "    $display(\"%0d %0d %0d %h\", $size(k.up), "
                       "$low(k.up), $high(k.up), k.up[5]);\n"
                       "    $display(\"%0d %0d %0d %h\", $size(k.down), "
                       "$low(k.down), $high(k.down), k.down[7]);\n"
                       "    $display(\"%0d %0d %h\", $size(k.grid, 1), "
                       "$size(k.grid, 2), k.grid[5][1]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "6 0 5 0aaa\n6 2 7 0bbb\n6 2 0ccc\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(ClassParameterWithoutDefaultSim, DerivedClassForwardsItsOwnToTheBase) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class Mem #(type T, int size);\n"
                       "  T words[size];\n"
                       "endclass\n"
                       "class Sub #(type U, int n) extends Mem#(U, n);\n"
                       "  U extra[n];\n"
                       "endclass\n"
                       "module t;\n"
                       "  Sub#(shortint, 6) s;\n"
                       "  initial begin\n"
                       "    s = new;\n"
                       "    s.words[5] = 16'h0123;\n"
                       "    s.extra[5] = 16'h0456;\n"
                       "    $display(\"%0d %0d %h %h\", $size(s.words), "
                       "$size(s.extra), s.words[5], s.extra[5]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "6 6 0123 0456\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(ClassParameterWithoutDefaultSim,
     PackageAndModuleSpecializationsSizeTheirArrays) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package pk;\n"
                       "  class PMem #(type T, int size);\n"
                       "    T words[size];\n"
                       "  endclass\n"
                       "endpackage\n"
                       "module t;\n"
                       "  class MMem #(type T, int size);\n"
                       "    T words[size];\n"
                       "  endclass\n"
                       "  function automatic int local_size();\n"
                       "    MMem#(shortint, 7) h;\n"
                       "    h = new;\n"
                       "    return $size(h.words) * 100 + $bits(h.words[0]);\n"
                       "  endfunction\n"
                       "  pk::PMem#(byte, 5) held;\n"
                       "  initial begin\n"
                       "    held = new;\n"
                       "    $display(\"%0d %0d %0d\", $size(held.words), "
                       "$bits(held.words[0]), local_size());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "5 8 716\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(ClassParameterWithoutDefaultSim, TheValueReachesEveryOtherUseInTheBody) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("class Mem #(type T, int size);\n"
                 "  bit [size-1:0] v;\n"
                 "  T x;\n"
                 "  T q[$];\n"
                 "  T d[];\n"
                 "  localparam int twice = size * 2;\n"
                 "  static int cnt = size;\n"
                 "  typedef T elem_t;\n"
                 "  elem_t e;\n"
                 "  function int held(int a);\n"
                 "    T local_copy;\n"
                 "    local_copy = a;\n"
                 "    return local_copy;\n"
                 "  endfunction\n"
                 "  function int tb(); return $bits(T) + size; endfunction\n"
                 "endclass\n"
                 "module t;\n"
                 "  Mem#(shortint, 6) k;\n"
                 "  initial begin\n"
                 "    k = new;\n"
                 "    k.d = new[k.size];\n"
                 "    k.q.push_back(16'h1234);\n"
                 "    $display(\"%0d %0d %0d\", $bits(k.v), $bits(k.x), "
                 "$bits(k.e));\n"
                 "    $display(\"%0d %h %0d\", k.d.size(), k.q[0], "
                 "$bits(k.q[0]));\n"
                 "    $display(\"%0d %0d %0d %h\", k.twice, "
                 "Mem#(shortint, 6)::cnt, k.tb(), k.held(32'h12345678));\n"
                 "    $display(\"%0d %0d\", Mem#(shortint, 6)::size, "
                 "Mem#(shortint, 6)::twice);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "6 16 16\n6 1234 16\n12 6 22 00005678\n6 12\n");
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
