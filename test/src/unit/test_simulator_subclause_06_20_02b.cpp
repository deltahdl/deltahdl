#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ValueParameterSimulation, TypedefModuleParameterKeepsXAndZOfItsType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef logic [3:0] n4_t;\n"
                       "typedef integer i_t;\n"
                       "typedef struct packed {logic [3:0] a;} s4_t;\n"
                       "typedef struct packed {bit [3:0] a;} s2_t;\n"
                       "typedef bit [3:0] b4_t;\n"
                       "interface ifc;\n"
                       "  parameter n4_t IP = 4'bz1x0;\n"
                       "  parameter s2_t IQ = 4'bz1x0;\n"
                       "endinterface\n"
                       "module t;\n"
                       "  typedef logic [3:0] ln_t;\n"
                       "  typedef struct packed {bit [3:0] a;} ls_t;\n"
                       "  parameter n4_t P = 4'b1x0z;\n"
                       "  parameter i_t I = 'x;\n"
                       "  parameter integer J = 'x;\n"
                       "  parameter s4_t S = 4'b1x0z;\n"
                       "  parameter s2_t T = 4'b1x0z;\n"
                       "  parameter b4_t B = 4'b1x0z;\n"
                       "  parameter ln_t L = 4'b1x0z;\n"
                       "  parameter ls_t M = 4'b1x0z;\n"
                       "  ifc i();\n"
                       "  initial $display(\"%b %b %b %b %b %b %b %b %b %b\", "
                       "P, I[3:0], J[3:0], S, T, B, L, M, i.IP, i.IQ);\n"
                       "endmodule\n",
                       f),
            "1x0z xxxx xxxx 1x0z 1000 1000 1x0z 1000 z1x0 0100\n");
}

TEST(ValueParameterSimulation,
     TypedefParameterPortOverrideKeepsXAndZOfItsType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef logic [3:0] n4_t;\n"
                       "typedef struct packed {logic [3:0] a;} s4_t;\n"
                       "typedef struct packed {bit [3:0] a;} s2_t;\n"
                       "module m #(parameter s4_t S = 0, s2_t T = 0, "
                       "n4_t N = 0) ();\n"
                       "  initial $display(\"%b %b %b\", S, T, N);\n"
                       "endmodule\n"
                       "module t;\n"
                       "  m #(.S(4'b1x0z), .T(4'b1x0z), .N(4'bz0x1)) u();\n"
                       "endmodule\n",
                       f),
            "1x0z 1000 z0x1\n");
}

TEST(ValueParameterSimulation, TwoStateStructTypedefClassParameterTakesZero) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef struct packed {bit [3:0] a;} gb_t;\n"
                       "typedef struct packed {logic [3:0] a;} gl_t;\n"
                       "class C #(parameter gb_t K = 4'b1x0z, gl_t KL = "
                       "4'b1x0z);\n"
                       "  parameter gb_t G = 4'b1x0z;\n"
                       "  typedef struct packed {bit [3:0] a;} b_t;\n"
                       "  parameter b_t Q = 4'b1x0z;\n"
                       "endclass\n"
                       "class D;\n"
                       "  parameter gb_t G = 4'b1x0z;\n"
                       "  parameter gl_t GL = 4'b1x0z;\n"
                       "endclass\n"
                       "module t;\n"
                       "  initial $display(\"%b %b %b %b %b %b %b\", C#()::K, "
                       "C#()::KL, C#()::G, C#()::Q, C#(4'bz01x)::K, D::G, "
                       "D::GL);\n"
                       "endmodule\n",
                       f),
            "1000 1x0z 1000 1000 0010 1000 1x0z\n");
}

TEST(ValueParameterSimulation,
     StructTypedefPackageParameterTakesItsTypesState) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  typedef struct packed {bit [3:0] a;} pb_t;\n"
                       "  typedef struct packed {logic [3:0] a;} pl_t;\n"
                       "  parameter pb_t PB = 4'b1x0z;\n"
                       "  parameter pl_t PL = 4'b1x0z;\n"
                       "endpackage\n"
                       "module t;\n"
                       "  parameter p::pb_t Q = 4'b1x0z;\n"
                       "  initial $display(\"%b %b %b\", p::PB, p::PL, Q);\n"
                       "endmodule\n",
                       f),
            "1000 1x0z 1000\n");
}

TEST(ValueParameterSimulation, PackageAndUnitIntegralParameterRoundsAReal) {
  SimFixture f;
  EXPECT_EQ(RunCapture("parameter int CU = 2.6;\n"
                       "parameter int CN = -2.5;\n"
                       "package pk;\n"
                       "  parameter int I = 2.6;\n"
                       "  parameter real R = 2.6;\n"
                       "  parameter int J = R;\n"
                       "  parameter bit [3:0] B = 2.6;\n"
                       "  parameter time T = 2.6;\n"
                       "  parameter shortint N = -2.5;\n"
                       "endpackage\n"
                       "module t;\n"
                       "  initial $display(\"%0d %0d %0d %0d %0d %0d %0d "
                       "%0.1f\", pk::I, pk::J, pk::B, pk::T, pk::N, CU, CN, "
                       "pk::R);\n"
                       "endmodule\n",
                       f),
            "3 3 3 3 -3 3 -3 2.6\n");
}

TEST(ValueParameterSimulation, PackageAndUnitParameterOfASignedTypeIsSigned) {
  SimFixture f;
  EXPECT_EQ(RunCapture("parameter byte CB = -1;\n"
                       "package pk;\n"
                       "  parameter byte BY = -1;\n"
                       "  parameter shortint SI = -1;\n"
                       "  parameter longint LI = -2;\n"
                       "  parameter bit [7:0] U = -1;\n"
                       "endpackage\n"
                       "module t;\n"
                       "  int x, y, z;\n"
                       "  initial begin\n"
                       "    x = pk::BY;\n"
                       "    y = CB;\n"
                       "    z = pk::U;\n"
                       "    $display(\"%0d %0d %0d %0d %0d %0d %0d %0d %0d\", "
                       "pk::BY < 0, x, pk::SI, pk::LI, CB < 0, y, pk::U < 0, "
                       "z, pk::SI + 0);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 -1 -1 -2 1 -1 0 255 -1\n");
}

TEST(ValueParameterSimulation, TypeParameterTypedClassParameterTakesItsState) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class F #(type T = logic [3:0], T Q = 4'b1x0z);\n"
                       "  parameter T P = 4'b1x0z;\n"
                       "  function void show();\n"
                       "    $display(\"%b %b\", P, Q);\n"
                       "  endfunction\n"
                       "endclass\n"
                       "class G #(type T = bit [3:0]);\n"
                       "  parameter T P = 4'b1x0z;\n"
                       "endclass\n"
                       "typedef F#(bit [3:0]) FB;\n"
                       "module t;\n"
                       "  F#(bit [3:0]) h;\n"
                       "  initial begin\n"
                       "    h = new;\n"
                       "    $display(\"%b %b %b %b %b %b %b %b %b\", "
                       "F#(bit [3:0])::P, F#()::P, FB::P, h.P, "
                       "F#(bit [3:0])::Q, F#(bit [3:0], 4'bz1x0)::Q, "
                       "F#(logic [3:0], 4'bz1x0)::Q, G#()::P, "
                       "G#(logic [3:0])::P);\n"
                       "    h.show();\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1000 1x0z 1000 1000 1000 0100 z1x0 1000 1x0z\n1000 1000\n");
}

TEST(ValueParameterSimulation, TypeParameterTypedModuleParameterTakesItsState) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package pk;\n"
                       "  typedef bit [3:0] pb_t;\n"
                       "  typedef logic [3:0] pl_t;\n"
                       "endpackage\n"
                       "typedef bit [3:0] b4_t;\n"
                       "typedef logic [3:0] n4_t;\n"
                       "interface it #(type T = logic [3:0], T P = 4'b1x0z);\n"
                       "  parameter T Q = 4'bz1x0;\n"
                       "  initial #3 $display(\"%m %b %b\", P, Q);\n"
                       "endinterface\n"
                       "program pg #(type T = bit [3:0], T P = 4'bz1x0);\n"
                       "  initial #4 $display(\"%m %b\", P);\n"
                       "endprogram\n"
                       "module mt #(type T = int, T P = 'x);\n"
                       "  parameter T B = 4'b1x0z;\n"
                       "  initial $display(\"%m %0d %0d\", P, B);\n"
                       "endmodule\n"
                       "module m4 #(type T = logic [3:0], T P = 4'b1x0z);\n"
                       "  parameter type U = bit [3:0];\n"
                       "  parameter T B = 4'bz1x0;\n"
                       "  parameter U C = 4'bz1x0;\n"
                       "  if (1) begin : g\n"
                       "    parameter T D = 4'b1zx0;\n"
                       "  end\n"
                       "  initial #2 $display(\"%m %b %b %b %b\", P, B, C, "
                       "g.D);\n"
                       "endmodule\n"
                       "module t;\n"
                       "  typedef logic [3:0] l_t;\n"
                       "  typedef bit [3:0] lb_t;\n"
                       "  mt a();\n"
                       "  mt #(.T(bit [3:0]), .P(4'b1x0z)) b();\n"
                       "  mt #(.T(logic [3:0]), .P(4'b1x0z)) c();\n"
                       "  m4 d();\n"
                       "  m4 #(.T(bit [3:0])) e();\n"
                       "  m4 #(b4_t, 4'bz0x1) g();\n"
                       "  m4 #(.T(pk::pb_t)) h();\n"
                       "  m4 #(.T(lb_t)) i();\n"
                       "  it ia();\n"
                       "  it #(.T(bit [3:0])) ib();\n"
                       "  pg pa();\n"
                       "  pg #(.T(logic [3:0])) pb();\n"
                       "  pg #(.T(n4_t)) pc();\n"
                       "  pg #(.T(l_t)) pd();\n"
                       "  pg #(.T(pk::pl_t)) pe();\n"
                       "endmodule\n",
                       f),
            "t.a 0 8\nt.b 8 8\nt.c X X\n"
            "t.d 1x0z z1x0 0100 1zx0\nt.e 1000 0100 0100 1000\n"
            "t.g 0001 0100 0100 1000\nt.h 1000 0100 0100 1000\n"
            "t.i 1000 0100 0100 1000\n"
            "t.ia 1x0z z1x0\nt.ib 1000 0100\nt.pa 0100\nt.pb z1x0\n"
            "t.pc z1x0\nt.pd z1x0\nt.pe z1x0\n");
}

TEST(ValueParameterSimulation, TypeParameterTypedModuleParameterTakesItsReal) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module mr #(type T = real, T P = 7);\n"
                       "  parameter T B = 0.1;\n"
                       "  initial $display(\"%m %.12f %.12f %0d %0d\", P, B, "
                       "$bits(P), $bits(B));\n"
                       "endmodule\n"
                       "module ms #(type T = shortreal, T P = 0.1);\n"
                       "  initial #1 $display(\"%m %.12f %0d\", P, $bits(P));\n"
                       "endmodule\n"
                       "module t;\n"
                       "  mr a();\n"
                       "  mr #(.T(shortreal), .P(0.1)) b();\n"
                       "  ms c();\n"
                       "  ms #(.T(real)) d();\n"
                       "endmodule\n",
                       f),
            "t.a 7.000000000000 0.100000000000 64 64\n"
            "t.b 0.100000001490 0.100000001490 32 32\n"
            "t.c 0.100000001490 32\nt.d 0.100000000000 64\n");
}

TEST(ValueParameterSimulation, PackageArrayParameterElementsTakeTheirType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package pk;\n"
                       "  parameter bit [3:0] A [2] = '{4'b1x0z, 4'bz1x0};\n"
                       "  parameter logic [3:0] L [2] = '{4'b1x0z, 4'bz1x0};\n"
                       "  parameter int E [2] = '{9, 5};\n"
                       "endpackage\n"
                       "module t;\n"
                       "  initial $display(\"%b %b %b %b %0d %0d\", pk::A[0], "
                       "pk::A[1], pk::L[0], pk::L[1], pk::E[0], pk::E[1]);\n"
                       "endmodule\n",
                       f),
            "1000 0100 1x0z z1x0 9 5\n");
}

TEST(ValueParameterSimulation, TwoStateParameterFeedsAConstantWithXAndZAsZero) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package pk;\n"
                       "  parameter bit [7:0] Y = 8'bx000_0101;\n"
                       "  localparam int YY = Y;\n"
                       "endpackage\n"
                       "parameter bit [3:0] UZ = 4'b1x1x;\n"
                       "class C #(parameter bit [3:0] CW = 4'b1x1x);\n"
                       "  localparam int CD = CW;\n"
                       "  localparam int CE = CW + 1;\n"
                       "endclass\n"
                       "interface it #(parameter bit [3:0] W = 4'b1x1x);\n"
                       "  localparam int D = W;\n"
                       "  logic [W:0] v;\n"
                       "endinterface\n"
                       "module m #(parameter bit [3:0] W = 0);\n"
                       "  localparam int D = W;\n"
                       "  logic [W:0] v;\n"
                       "  initial $display(\"%m %0d %0d\", D, $bits(v));\n"
                       "endmodule\n"
                       "module t;\n"
                       "  parameter bit [3:0] Z = 4'b1x1x;\n"
                       "  parameter int K = 4'b1x1x;\n"
                       "  parameter logic [3:0] L = 4'b1x1x;\n"
                       "  localparam int ZZ = Z;\n"
                       "  localparam int S = Z + 1;\n"
                       "  localparam int LL = L;\n"
                       "  logic [Z:0] w;\n"
                       "  logic [K:0] k;\n"
                       "  logic [pk::Y:0] pv;\n"
                       "  logic [UZ:0] u;\n"
                       "  it i();\n"
                       "  if (1) begin : g\n"
                       "    parameter bit [3:0] GZ = 4'bz1z1;\n"
                       "    logic [GZ:0] gv;\n"
                       "  end\n"
                       "  m #(.W(4'b1x1x)) a();\n"
                       "  m #(4'bz0x1) b();\n"
                       "  initial #1 $display(\"%0d %0d %b %0d %0d %0d %0d "
                       "%0d %0d %0d %0d %0d %0d %0d\", ZZ, S, L, LL, $bits(w), "
                       "$bits(k), $bits(pv), pk::YY, $bits(u), i.D, "
                       "$bits(i.v), $bits(g.gv), C#()::CD, C#()::CE);\n"
                       "endmodule\n",
                       f),
            "t.a 10 11\nt.b 1 2\n10 11 1x1x 10 11 11 6 5 11 10 11 6 10 11\n");
}

TEST(ValueParameterSimulation,
     ShortrealParameterFeedsAConstantAtSinglePrecision) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef shortreal sr_t;\n"
                       "class C #(parameter shortreal CS = 0.1);\n"
                       "  localparam real CD = CS;\n"
                       "endclass\n"
                       "module mr #(type T = real, T P = 0.1);\n"
                       "  localparam real D = P;\n"
                       "  localparam bit EQ = (P == 0.1);\n"
                       "  initial $display(\"%m %.12f %0d\", D, EQ);\n"
                       "endmodule\n"
                       "module mo #(parameter shortreal R = 1.0);\n"
                       "  localparam real D = R;\n"
                       "  localparam bit EQ = (R == 0.1);\n"
                       "  initial $display(\"%m %.12f %0d\", D, EQ);\n"
                       "endmodule\n"
                       "module t;\n"
                       "  parameter shortreal S = 0.1;\n"
                       "  parameter sr_t TS = 0.1;\n"
                       "  parameter real R = 0.1;\n"
                       "  localparam real D = S;\n"
                       "  localparam bit EQ = (S == 0.1);\n"
                       "  localparam real TD = TS;\n"
                       "  localparam real RD = R;\n"
                       "  localparam bit REQ = (R == 0.1);\n"
                       "  if (1) begin : g\n"
                       "    parameter shortreal GS = 0.1;\n"
                       "    localparam real GD = GS;\n"
                       "  end\n"
                       "  mr #(.T(shortreal), .P(0.1)) a();\n"
                       "  mr b();\n"
                       "  mo #(.R(0.1)) c();\n"
                       "  initial #1 $display(\"%.12f %0d %.12f %.12f %0d "
                       "%.12f %.12f\", D, EQ, TD, RD, REQ, g.GD, C#()::CD);\n"
                       "endmodule\n",
                       f),
            "t.a 0.100000001490 0\nt.b 0.100000000000 1\n"
            "t.c 0.100000001490 0\n"
            "0.100000001490 0 0.100000001490 0.100000000000 1 "
            "0.100000001490 0.100000001490\n");
}

TEST(ValueParameterSimulation, FourStateParameterKeepsXInAConstantComparison) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter logic [3:0] L = 4'b1x1x;\n"
                       "  parameter bit [3:0] B = 4'b1x1x;\n"
                       "  localparam bit EQ = (L == 4'b1010);\n"
                       "  localparam bit CE = (L === 4'b1010);\n"
                       "  localparam bit LE = (4'b1x1x == 4'b1010);\n"
                       "  localparam bit LCE = (4'b1x1x === 4'b1010);\n"
                       "  localparam bit BE = (B == 4'b1010);\n"
                       "  localparam bit BCE = (B === 4'b1010);\n"
                       "  if (L == 4'b1010) begin : a\n"
                       "    initial $display(\"a\");\n"
                       "  end\n"
                       "  if (L === 4'b1010) begin : b\n"
                       "    initial $display(\"b\");\n"
                       "  end\n"
                       "  if (4'b1x1x === 4'b1010) begin : c\n"
                       "    initial $display(\"c\");\n"
                       "  end\n"
                       "  if (4'b1x1x == 4'b1010) begin : d\n"
                       "    initial $display(\"d\");\n"
                       "  end\n"
                       "  if (B === 4'b1010) begin : e\n"
                       "    initial $display(\"e\");\n"
                       "  end\n"
                       "  if (L !== 4'b1010) begin : g\n"
                       "    initial $display(\"g\");\n"
                       "  end\n"
                       "  initial #1 $display(\"%0d %0d %0d %0d %0d %0d\", EQ, "
                       "CE, LE, LCE, BE, BCE);\n"
                       "endmodule\n",
                       f),
            "e\ng\n0 0 0 0 1 1\n");
}

TEST(ValueParameterSimulation, ConstantOfAFourStateParameterKeepsXAndZ) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package pk;\n"
                       "  parameter logic [3:0] PL = 4'bz1x0;\n"
                       "  localparam logic [3:0] PM = PL;\n"
                       "endpackage\n"
                       "module m4 #(parameter logic [3:0] P = 0);\n"
                       "  initial $display(\"%m %b\", P);\n"
                       "endmodule\n"
                       "module t;\n"
                       "  parameter logic [3:0] L = 4'b1x1z;\n"
                       "  localparam logic [3:0] M = L;\n"
                       "  localparam integer J = L;\n"
                       "  localparam bit [3:0] B = L;\n"
                       "  localparam int I = L;\n"
                       "  m4 #(.P(L)) a();\n"
                       "  m4 #(L) b();\n"
                       "  initial #1 $display(\"%b %b %b %0d %b\", M, J, B, I, "
                       "pk::PM);\n"
                       "endmodule\n",
                       f),
            "t.a 1x1z\nt.b 1x1z\n"
            "1x1z 00000000000000000000000000001x1z 1010 10 z1x0\n");
}

TEST(ValueParameterSimulation, TwoStateParameterOfAFourStateNameTakesZero) {
  SimFixture f;
  EXPECT_EQ(RunCapture("parameter logic [3:0] UL = 4'b1x1x;\n"
                       "parameter bit [3:0] UB = UL;\n"
                       "package pk;\n"
                       "  parameter logic [3:0] PL = 4'bz1z1;\n"
                       "  parameter bit [3:0] PB = PL;\n"
                       "endpackage\n"
                       "class C #(parameter logic [3:0] CL = 4'b1x1x,\n"
                       "          parameter bit [3:0] CW = CL);\n"
                       "  localparam bit [3:0] CB = CL;\n"
                       "endclass\n"
                       "interface it #(parameter logic [3:0] IL = 4'b1x1x);\n"
                       "  localparam bit [3:0] IW = IL;\n"
                       "  logic [IW:0] v;\n"
                       "endinterface\n"
                       "module w;\n"
                       "  import pk::*;\n"
                       "  localparam bit [3:0] WB = PL;\n"
                       "  logic [WB:0] v;\n"
                       "  initial $display(\"%m %0d\", $bits(v));\n"
                       "endmodule\n"
                       "module m #(parameter bit [3:0] W = 0);\n"
                       "  logic [W:0] v;\n"
                       "  initial $display(\"%m %0d %0d\", W, $bits(v));\n"
                       "endmodule\n"
                       "module t;\n"
                       "  import pk::PL;\n"
                       "  parameter logic [3:0] L = 4'b1x1x;\n"
                       "  parameter logic [3:0] L2 = L;\n"
                       "  parameter logic [3:0] LZ = 4'bz1z1;\n"
                       "  localparam bit [3:0] SW = C#(.CL(LZ))::CW;\n"
                       "  localparam bit [3:0] BL = L;\n"
                       "  localparam int IL = L;\n"
                       "  localparam bit [7:0] CC = {L, L};\n"
                       "  localparam bit [3:0] B2 = L2;\n"
                       "  localparam bit [3:0] MU = UL;\n"
                       "  localparam bit [3:0] QB = pk::PL;\n"
                       "  localparam bit [3:0] IB = PL;\n"
                       "  logic [BL:0] vb;\n"
                       "  logic [IL:0] vi;\n"
                       "  logic [CC:0] vc;\n"
                       "  logic [B2:0] v2;\n"
                       "  logic [UB:0] vu;\n"
                       "  logic [MU:0] vm;\n"
                       "  logic [pk::PB:0] vp;\n"
                       "  logic [QB:0] vq;\n"
                       "  logic [IB:0] vn;\n"
                       "  logic [C#()::CW:0] vw;\n"
                       "  logic [C#()::CB:0] vx;\n"
                       "  logic [C#(LZ)::CB:0] vy;\n"
                       "  logic [SW:0] vs;\n"
                       "  w uw();\n"
                       "  it i();\n"
                       "  if (1) begin : g\n"
                       "    localparam bit [3:0] GB = L;\n"
                       "    logic [GB:0] gv;\n"
                       "  end\n"
                       "  m #(.W(L)) a();\n"
                       "  m #(L) b();\n"
                       "  initial #1 $display(\"%0d %0d %0d %0d %0d %0d %0d "
                       "%0d %0d %0d %0d %0d %0d %0d %0d %0d\", BL, $bits(vb), "
                       "$bits(vi), $bits(vc), $bits(v2), $bits(vu), $bits(vm), "
                       "$bits(vp), $bits(vq), $bits(vn), $bits(vw), $bits(vx), "
                       "$bits(i.v), $bits(g.gv), $bits(vy), $bits(vs));\n"
                       "endmodule\n",
                       f),
            "t.uw 6\nt.a 10 11\nt.b 10 11\n"
            "10 11 11 171 11 11 11 6 6 6 11 11 11 11 6 6\n");
}

TEST(ValueParameterSimulation, NameHidingAFourStateParameterKeepsItsValue) {
  SimFixture f;
  EXPECT_EQ(RunCapture("parameter logic [3:0] L = 4'b1x1x;\n"
                       "package pk;\n"
                       "  parameter logic [3:0] Q = 4'bz1z1;\n"
                       "endpackage\n"
                       "module e;\n"
                       "  typedef enum int {A, B, C, L} e_t;\n"
                       "  localparam int H = L;\n"
                       "  logic [H:0] v;\n"
                       "  initial #1 $display(\"%m %0d %0d\", H, $bits(v));\n"
                       "endmodule\n"
                       "module w;\n"
                       "  import pk::*;\n"
                       "  typedef enum int {A, Q} e_t;\n"
                       "  localparam int H = Q;\n"
                       "  logic [H:0] v;\n"
                       "  initial #2 $display(\"%m %0d %0d\", H, $bits(v));\n"
                       "endmodule\n"
                       "module fx;\n"
                       "  function automatic int fa(int L);\n"
                       "    return L;\n"
                       "  endfunction\n"
                       "  function automatic int fb();\n"
                       "    int L = 3;\n"
                       "    return L;\n"
                       "  endfunction\n"
                       "  function automatic int fc();\n"
                       "    for (int L = 4; L < 5; L++) return L;\n"
                       "  endfunction\n"
                       "  localparam int A = fa(2);\n"
                       "  localparam int B = fb();\n"
                       "  localparam int C = fc();\n"
                       "  logic [A:0] a;\n"
                       "  logic [B:0] b;\n"
                       "  logic [C:0] c;\n"
                       "  initial #3 $display(\"%m %0d %0d %0d\", $bits(a), "
                       "$bits(b), $bits(c));\n"
                       "endmodule\n"
                       "module mo #(parameter int W = 0);\n"
                       "  logic [W:0] v;\n"
                       "  initial #5 $display(\"%m %0d %0d\", W, $bits(v));\n"
                       "endmodule\n"
                       "module po;\n"
                       "  typedef enum int {A, B, C, L} e_t;\n"
                       "  mo #(.W(L)) a();\n"
                       "  mo #(L) b();\n"
                       "endmodule\n"
                       "module t;\n"
                       "  import pk::*;\n"
                       "  localparam int HL = L;\n"
                       "  localparam int HQ = Q;\n"
                       "  logic [HL:0] vl;\n"
                       "  logic [HQ:0] vq;\n"
                       "  for (genvar L = 0; L < 2; L++) begin : g\n"
                       "    localparam int H = L;\n"
                       "    logic [H:0] v;\n"
                       "  end\n"
                       "  for (genvar Q = 2; Q < 3; Q++) begin : h\n"
                       "    localparam int H = Q;\n"
                       "    logic [H:0] v;\n"
                       "  end\n"
                       "  e ue();\n"
                       "  w uw();\n"
                       "  fx uf();\n"
                       "  po up();\n"
                       "  initial #4 $display(\"%0d %0d %0d %0d %0d\", "
                       "$bits(vl), $bits(vq), $bits(g[0].v), $bits(g[1].v), "
                       "$bits(h[2].v));\n"
                       "endmodule\n",
                       f),
            "t.ue 3 4\nt.uw 1 2\nt.uf 3 4 5\n11 6 1 2 3\n"
            "t.up.a 3 4\nt.up.b 3 4\n");
}

}  // namespace
