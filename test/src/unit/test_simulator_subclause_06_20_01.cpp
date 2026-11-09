#include <gtest/gtest.h>

#include <cstdint>
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
          "Q = 4'b1x0z);\n"
          "  localparam struct packed {logic [3:0] a;} S = 4'bz01x;\n"
          "endclass\n"
          "class D;\n"
          "  parameter struct {int a; int b;} R = '{a: 4, b: 9};\n"
          "  localparam union packed {bit [3:0] u; bit [3:0] w;} "
          "U = 4'b1x0z;\n"
          "endclass\n"
          "module t;\n"
          "  initial $display(\"%b %b %b %b %0d %0d %b\", C#()::P, C#()::Q, "
          "C#()::S, C#(4'h6)::P, D::R.a, D::R.b, D::U);\n"
          "endmodule\n",
          f),
      "1000 1x0z z01x 0110 4 9 1000\n");
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

}  // namespace
