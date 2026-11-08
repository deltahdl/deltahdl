#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ValueParameterSim, RealParameterKeepsItsFraction) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter real R = 2.5;\n"
                       "  initial $display(\"%g\", R);\n"
                       "endmodule\n",
                       f),
            "2.5\n");
}

TEST(ValueParameterSim, RealLocalparamKeepsItsFraction) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  localparam real R = 0.125;\n"
                       "  initial $display(\"%g\", R);\n"
                       "endmodule\n",
                       f),
            "0.125\n");
}

TEST(ValueParameterSim, RealParameterPortKeepsItsFraction) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t #(parameter real R = 1.5);\n"
                       "  initial $display(\"%g\", R);\n"
                       "endmodule\n",
                       f),
            "1.5\n");
}

TEST(ValueParameterSim, RealParameterWithoutAFractionIsStillReal) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter real R = 2;\n"
                       "  initial $display(\"%g\", R / 4);\n"
                       "endmodule\n",
                       f),
            "0.5\n");
}

TEST(ValueParameterSim, IntegerParameterFromRealConstantStillRounds) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter int N = 2.5;\n"
                       "  initial $display(\"%0d\", N);\n"
                       "endmodule\n",
                       f),
            "3\n");
}

TEST(ValueParameterSim, WideLocalparamKeepsEveryWordOfItsValue) {
  SimFixture f;
  auto* hi = RunAndFindVar(
      "module t;\n"
      "  localparam logic [95:0] P = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "  int hi, mid, lo;\n"
      "  initial begin\n"
      "    hi = P[95:64];\n"
      "    mid = P[63:32];\n"
      "    lo = P[31:0];\n"
      "  end\n"
      "endmodule\n",
      f, "hi");
  ASSERT_NE(hi, nullptr);
  EXPECT_EQ(hi->value.ToUint64(), 0x01234567u);
  auto* mid = f.ctx.FindVariable("mid");
  auto* lo = f.ctx.FindVariable("lo");
  ASSERT_NE(mid, nullptr);
  ASSERT_NE(lo, nullptr);
  EXPECT_EQ(mid->value.ToUint64(), 0x89ABCDEFu);
  EXPECT_EQ(lo->value.ToUint64(), 0x00112233u);
  EXPECT_FALSE(f.has_errors);
}

TEST(ValueParameterSim, WideParameterOperandCarriesItsHighWord) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  parameter logic [95:0] P = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "  int y;\n"
      "  initial y = P >> 64;\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0x01234567u);
  EXPECT_FALSE(f.has_errors);
}

TEST(ValueParameterSim, WideLocalparamSetFromAWideParameterKeepsEveryWord) {
  SimFixture f;
  auto* hi = RunAndFindVar(
      "module t;\n"
      "  localparam logic [95:0] P = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "  localparam logic [95:0] Q = P >> 8;\n"
      "  int hi;\n"
      "  initial hi = Q[95:64];\n"
      "endmodule\n",
      f, "hi");
  ASSERT_NE(hi, nullptr);
  EXPECT_EQ(hi->value.ToUint64(), 0x00012345u);
  EXPECT_FALSE(f.has_errors);
}

TEST(ValueParameterSim, WideParameterOverriddenAtTheInstanceKeepsEveryWord) {
  SimFixture f;
  auto* hi = RunAndFindVar(
      "module c #(parameter logic [95:0] P = 96'h0);\n"
      "  int hi, lo;\n"
      "  initial begin\n"
      "    hi = P[95:64];\n"
      "    lo = P[31:0];\n"
      "  end\n"
      "endmodule\n"
      "module t;\n"
      "  c #(.P(96'h0123_4567_89AB_CDEF_0011_2233)) u();\n"
      "endmodule\n",
      f, "u.hi");
  ASSERT_NE(hi, nullptr);
  EXPECT_EQ(hi->value.ToUint64(), 0x01234567u);
  auto* lo = f.ctx.FindVariable("u.lo");
  ASSERT_NE(lo, nullptr);
  EXPECT_EQ(lo->value.ToUint64(), 0x00112233u);
  EXPECT_FALSE(f.has_errors);
}

TEST(ValueParameterSim, WideParameterOverrideNamingTheParentsParameter) {
  SimFixture f;
  auto* hi = RunAndFindVar(
      "module c #(parameter logic [95:0] P = 96'h0);\n"
      "  int hi;\n"
      "  initial hi = P[95:64];\n"
      "endmodule\n"
      "module t;\n"
      "  localparam logic [95:0] K = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "  c #(.P(K)) u();\n"
      "endmodule\n",
      f, "u.hi");
  ASSERT_NE(hi, nullptr);
  EXPECT_EQ(hi->value.ToUint64(), 0x01234567u);
  EXPECT_FALSE(f.has_errors);
}

TEST(ValueParameterSim, UntypedParameterIsAsWideAsItsSizedLiteral) {
  SimFixture f;
  std::string printed = RunCapture(
      "module t;\n"
      "  parameter p1 = 13'h7e;\n"
      "  parameter [31:0] dec_const = 1'b1;\n"
      "  parameter newconst3 = 3'h4;\n"
      "  parameter newconst4 = 4;\n"
      "  parameter signed [3:0] mux_selector = 0;\n"
      "  parameter real r1 = 3.5e17;\n"
      "  parameter msb = 7;\n"
      "  parameter e = 25, f = 9;\n"
      "  parameter byte_size = 8, byte_mask = byte_size - 1;\n"
      "  initial begin\n"
      "    $display(\"p1=%0d dec=%0d new3=%0d new4=%0d msel=%0d rbits=%0d\",\n"
      "             $bits(p1), $bits(dec_const), $bits(newconst3),\n"
      "             $bits(newconst4), $bits(mux_selector), $bits(r1));\n"
      "    $display(\"sel=%0d s=%0d e=%0d f=%0d bm=%0d p1=%h new3=%b\",\n"
      "             $signed(4'b1100 + mux_selector), msb, e, f, byte_mask,\n"
      "             p1, newconst3);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(printed,
            "p1=13 dec=32 new3=3 new4=32 msel=4 rbits=64\n"
            "sel=-4 s=7 e=25 f=9 bm=7 p1=007e new3=100\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(ValueParameterSim, UntypedParameterPortTakesTheWidthOfItsFinalValue) {
  SimFixture f;
  std::string printed = RunCapture(
      "module c #(parameter P = 13'h7e);\n"
      "  initial $display(\"P=%0d\", $bits(P));\n"
      "endmodule\n"
      "module t;\n"
      "  parameter N = -1;\n"
      "  parameter signed S = 4'sd7;\n"
      "  c u1();\n"
      "  c #(.P(5'd9)) u2();\n"
      "  initial begin\n"
      "    #1 $display(\"N=%0d nb=%0d S=%0d sb=%0d\", N, $bits(N), S, "
      "$bits(S));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(printed, "P=13\nP=5\nN=-1 nb=32 S=7 sb=4\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(ValueParameterSim, UntypedParameterWithARealValueIsReal) {
  SimFixture f;
  std::string printed = RunCapture(
      "module t;\n"
      "  parameter r = 5.7;\n"
      "  parameter e = 25, f = 9;\n"
      "  parameter average_delay = (r + f) / 2;\n"
      "  parameter real r1 = 3.5e17;\n"
      "  parameter twice = r1 * 2;\n"
      "  parameter int ri = r;\n"
      "  initial $display(\"r=%f avg=%0d avgr=%f twice=%0d ri=%0d e=%0d\", r,\n"
      "                   $rtoi(average_delay), average_delay,\n"
      "                   twice == 7.0e17, ri, e);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(printed, "r=5.700000 avg=7 avgr=7.350000 twice=1 ri=6 e=25\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(ValueParameterSim, UntypedParameterPortWithARealDefaultIsReal) {
  SimFixture f;
  std::string printed = RunCapture(
      "module c #(parameter real a = 1.5, parameter b = a * 2,\n"
      "           parameter c = 0.25);\n"
      "  initial $display(\"b=%f c=%f\", b, c);\n"
      "endmodule\n"
      "module t;\n"
      "  c u();\n"
      "endmodule\n",
      f);
  EXPECT_EQ(printed, "b=3.000000 c=0.250000\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(ValueParameterSim, RealClassParamKeepsItsFractionInEverySpecialization) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("class Mem #(int size = 4, real D = 1.5);\n"
                 "  function real d(); return D; endfunction\n"
                 "  function real twice(); return D * 2; endfunction\n"
                 "endclass\n"
                 "module t;\n"
                 "  typedef Mem #(1024) Kbyte;\n"
                 "  Mem m; Mem #(.D(2.25)) o;\n"
                 "  initial begin\n"
                 "    m = new; o = new;\n"
                 "    $display(\"%g %g %g %g %g\", m.d(), o.d(), m.twice(),\n"
                 "             o.twice(), Kbyte::D);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "1.5 2.25 3 4.5 1.5\n");
}

TEST(ValueParameterSim, IntegerClassParamFromRealConstantRounds) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("class C #(int N = 2.5);\n"
                 "  function int n(); return N; endfunction\n"
                 "endclass\n"
                 "module t;\n"
                 "  C c;\n"
                 "  initial begin c = new; $display(\"%0d\", c.n()); end\n"
                 "endmodule\n",
                 f),
      "3\n");
}

TEST(ValueParameterSim, NamedBlockVariableSizedByParameter) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter W = 16;\n"
                       "  localparam int L = 12;\n"
                       "  initial begin : blk\n"
                       "    logic [W-1:0] b;\n"
                       "    logic [L-1:0] c;\n"
                       "    b = '1; c = '1;\n"
                       "    $display(\"%0d %0d %0d\", b, c, $bits(b));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "65535 4095 16\n");
}

TEST(ValueParameterSim, SubroutineLocalSizedByParameter) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter W = 16;\n"
                       "  function int fs();\n"
                       "    logic [W-1:0] r; r = '1; return r;\n"
                       "  endfunction\n"
                       "  function automatic int fa();\n"
                       "    logic [W-1:0] r; r = '1; return r;\n"
                       "  endfunction\n"
                       "  task tk(output int o);\n"
                       "    logic [W-1:0] q; q = '1; o = q;\n"
                       "  endtask\n"
                       "  initial begin\n"
                       "    int o;\n"
                       "    tk(o);\n"
                       "    $display(\"%0d %0d %0d\", fs(), fa(), o);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "65535 65535 65535\n");
}

TEST(ValueParameterSim, ForInitVariableSizedByParameter) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter W = 16;\n"
                       "  function automatic int last();\n"
                       "    int n = 0; int s = 0;\n"
                       "    for (logic [W-1:0] i = '1; n < 2; i++) begin\n"
                       "      s += i; n++;\n"
                       "    end\n"
                       "    return s;\n"
                       "  endfunction\n"
                       "  initial begin\n"
                       "    int n;\n"
                       "    n = 0;\n"
                       "    for (logic [W-1:0] i = '1; n < 2; i++) begin\n"
                       "      $display(\"%0d\", i); n++;\n"
                       "    end\n"
                       "    $display(\"%0d\", last());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "65535\n0\n65535\n");
}

TEST(ValueParameterSim, BlockVariableSizedByEachInstancesParameter) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m #(parameter W = 4, parameter D = 1);\n"
                       "  initial begin : b\n"
                       "    logic [W-1:0] v;\n"
                       "    #D v = '1;\n"
                       "    $display(\"%0d\", v);\n"
                       "  end\n"
                       "endmodule\n"
                       "module t;\n"
                       "  m #(.W(8), .D(1)) a();\n"
                       "  m #(.W(3), .D(2)) c();\n"
                       "endmodule\n",
                       f),
            "255\n7\n");
}

TEST(ValueParameterSimulation,
     BlockAndSubroutineParametersTakeTheirValuesType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child;\n"
                       "  parameter W = 2;\n"
                       "  function int fq();\n"
                       "    parameter FQ = 11;\n"
                       "    return FQ;\n"
                       "  endfunction\n"
                       "  task tk;\n"
                       "    localparam TL = 9;\n"
                       "    $display(\"%0d\", TL);\n"
                       "  endtask\n"
                       "  initial begin : blk\n"
                       "    parameter Q = 3;\n"
                       "    parameter D = W * 10;\n"
                       "    $display(\"%0d %0d %0d\", Q, D, fq());\n"
                       "    tk;\n"
                       "  end\n"
                       "endmodule\n"
                       "module top;\n"
                       "  child #(.W(4)) u();\n"
                       "endmodule\n",
                       f),
            "3 40 11\n9\n");
}

TEST(ValueParameterSimulation, BlockParameterTakesRealAndWrittenSigning) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  initial begin\n"
          "    parameter R = 1.5;\n"
          "    parameter signed S = 8'hF0;\n"
          "    parameter unsigned U = -1;\n"
          "    parameter byte B = 300;\n"
          "    parameter [3:0] N = 25;\n"
          "    $display(\"%f %0d %0d %0d %0d %0d\", R, $bits(S), S, U, B, "
          "N);\n"
          "  end\n"
          "endmodule\n",
          f),
      "1.500000 8 -16 4294967295 44 9\n");
}

TEST(ValueParameterSimulation, ClassParameterOfATypedefTypeIsConverted) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef bit [3:0] nib;\n"
                       "class C #(nib P = 12'hFFF);\n"
                       "  function int get(); return P; endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  initial begin\n"
                       "    static C #() c = new;\n"
                       "    $display(\"%0d\", c.get());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "15\n");
}

TEST(ValueParameterSimulation, PackageEnumMemberFromATypedefParameter) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  typedef bit [3:0] nib;\n"
                       "  parameter nib P = 12'hFFF;\n"
                       "  parameter nib [1:0] W = 20'hFFFFF;\n"
                       "  typedef enum int {A = P, B = W} e;\n"
                       "endpackage\n"
                       "module t;\n"
                       "  initial $display(\"%0d %0d\", p::A, p::B);\n"
                       "endmodule\n",
                       f),
            "15 255\n");
}

TEST(ValueParameterSimulation, ClassParameterOfARealTypedefStaysReal) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef real r_t;\n"
                       "class C #(r_t R = 2.5);\n"
                       "  function real get(); return R; endfunction\n"
                       "endclass\n"
                       "module t;\n"
                       "  initial begin\n"
                       "    static C #() c = new;\n"
                       "    $display(\"%g\", c.get());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "2.5\n");
}

TEST(ValueParameterSimulation, NestedClassParameterOfItsOwnTypedef) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class Outer;\n"
                       "  class Inner;\n"
                       "    typedef bit [3:0] t;\n"
                       "    localparam t P = 12'hFFF;\n"
                       "    function int get(); return P; endfunction\n"
                       "  endclass\n"
                       "endclass\n"
                       "module top;\n"
                       "  Outer::Inner in = new;\n"
                       "  initial $display(\"%0d\", in.get());\n"
                       "endmodule\n",
                       f),
            "15\n");
}

TEST(ValueParameterSimulation, TwoStateModuleParameterTakesXAndZAsZero) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  parameter bit [3:0] P = 4'b1x0z;\n"
                 "  parameter int I = 'x;\n"
                 "  parameter byte B = 8'bz1x1_0110;\n"
                 "  localparam shortint S = 16'hzz12;\n"
                 "  localparam longint L = 'z;\n"
                 "  parameter logic [3:0] K = 4'b1x0z;\n"
                 "  initial $display(\"%b %0d %b %h %0d %b\", P, I, B, S, "
                 "L, K);\n"
                 "endmodule\n",
                 f),
      "1000 0 01010110 0012 0 1x0z\n");
}

TEST(ValueParameterSimulation, TwoStateParameterPortOverrideTakesXAndZAsZero) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m #(parameter int W = 7);\n"
                       "  initial $display(\"%0d\", W);\n"
                       "endmodule\n"
                       "module t;\n"
                       "  m #(.W(32'b1z1x)) u();\n"
                       "endmodule\n",
                       f),
            "10\n");
}

TEST(ValueParameterSimulation, TwoStatePackageParameterTakesXAndZAsZero) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package pk;\n"
                       "  typedef bit [3:0] pn_t;\n"
                       "  parameter bit [3:0] PP = 4'b1x0z;\n"
                       "  parameter int PI = 'z;\n"
                       "  parameter pn_t PN = 4'bx1z1;\n"
                       "  parameter logic [3:0] PL = 4'b1x0z;\n"
                       "endpackage\n"
                       "module t;\n"
                       "  initial $display(\"%b %0d %b %b\", pk::PP, pk::PI, "
                       "pk::PN, pk::PL);\n"
                       "endmodule\n",
                       f),
            "1000 0 0101 1x0z\n");
}

TEST(ValueParameterSimulation, TwoStateCompilationUnitParameterTakesZero) {
  SimFixture f;
  EXPECT_EQ(RunCapture("parameter bit [3:0] CU = 4'bz1x1;\n"
                       "parameter logic [3:0] CL = 4'bz1x1;\n"
                       "module t;\n"
                       "  initial $display(\"%b %b\", CU, CL);\n"
                       "endmodule\n",
                       f),
            "0101 z1x1\n");
}

TEST(ValueParameterSimulation, TwoStateClassParameterTakesXAndZAsZero) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef bit [3:0] nib_t;\n"
                       "class C #(parameter int CI = 'x, nib_t CN = 4'b1xx1);\n"
                       "  parameter bit [7:0] CB = 8'hx5;\n"
                       "  parameter logic [3:0] CL = 4'b1x0z;\n"
                       "endclass\n"
                       "module t;\n"
                       "  C h;\n"
                       "  initial begin\n"
                       "    h = new;\n"
                       "    $display(\"%0d %b %b %b %b\", C#()::CI, C#()::CN, "
                       "C#()::CB, C#()::CL, h.CN);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "0 1001 00000101 1x0z 1001\n");
}

TEST(ValueParameterSimulation, SpecializationActualIsConvertedToItsType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class C #(parameter int CI = 1, bit [3:0] CN = 3);\n"
                       "endclass\n"
                       "module t;\n"
                       "  initial $display(\"%0d %0d %b %b\", C#(4'bxx11)::CI, "
                       "$bits(C#(4'b0011)::CI), C#(1, 8'hfe)::CN, "
                       "C#(.CN(4'bz1x1))::CN);\n"
                       "endmodule\n",
                       f),
            "3 32 1110 0101\n");
}

TEST(ValueParameterSimulation, TwoStateInterfaceAndGenerateParametersTakeZero) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc;\n"
                       "  parameter int II = 32'hxxxx_0003;\n"
                       "endinterface\n"
                       "module t;\n"
                       "  ifc i();\n"
                       "  if (1) begin : g\n"
                       "    parameter bit [3:0] GP = 4'b1x1x;\n"
                       "  end\n"
                       "  initial $display(\"%h %b\", i.II, g.GP);\n"
                       "endmodule\n",
                       f),
            "00000003 1010\n");
}

TEST(ValueParameterSimulation, TwoStateProgramParameterTakesXAndZAsZero) {
  SimFixture f;
  EXPECT_EQ(RunCapture("program pg;\n"
                       "  parameter byte PB = 8'bzzzz_1111;\n"
                       "  initial $display(\"%b\", PB);\n"
                       "endprogram\n"
                       "module t;\n"
                       "  pg p();\n"
                       "endmodule\n",
                       f),
            "00001111\n");
}

TEST(ValueParameterSimulation, TimeParameterIsSixtyFourUnsignedBits) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  parameter time T = 5;\n"
                 "  parameter time N = -1;\n"
                 "  parameter time R = 2.6;\n"
                 "  initial $display(\"%0d %0d %0d %0d %0d\", T, $bits(T), "
                 "N, R, N > 0);\n"
                 "endmodule\n",
                 f),
      "5 64 18446744073709551615 3 1\n");
}

TEST(ValueParameterSimulation, ShortrealParameterHoldsASinglePrecisionValue) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter shortreal S = 1.5;\n"
                       "  parameter shortreal M = 0.1;\n"
                       "  localparam shortreal L = 16777217;\n"
                       "  parameter shortreal I = 7;\n"
                       "  initial $display(\"%g %0d %.12f %.1f %g\", S, "
                       "$bits(S), M, L, I / 4);\n"
                       "endmodule\n",
                       f),
            "1.5 32 0.100000001490 16777216.0 1.75\n");
}

TEST(ValueParameterSimulation,
     ShortrealParameterPortOverrideIsSinglePrecision) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m #(parameter shortreal R = 1.0);\n"
                       "  initial $display(\"%.12f %0d\", R, $bits(R));\n"
                       "endmodule\n"
                       "module t;\n"
                       "  m #(.R(0.1)) u();\n"
                       "endmodule\n",
                       f),
            "0.100000001490 32\n");
}

TEST(ValueParameterSimulation, ShortrealPackageAndClassParameters) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package pk;\n"
                       "  parameter shortreal PS = 0.1;\n"
                       "endpackage\n"
                       "class C #(shortreal CS = 0.1);\n"
                       "  localparam shortreal LS = 0.1;\n"
                       "endclass\n"
                       "module t;\n"
                       "  initial $display(\"%.12f %0d %.12f %0d %.12f\", "
                       "pk::PS, $bits(pk::PS), C#()::CS, $bits(C#()::CS), "
                       "C#()::LS);\n"
                       "endmodule\n",
                       f),
            "0.100000001490 32 0.100000001490 32 0.100000001490\n");
}

TEST(ValueParameterSimulation, ShortrealTypedefParameterIsSinglePrecision) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef shortreal sr_t;\n"
                       "package pk;\n"
                       "  typedef shortreal psr_t;\n"
                       "  parameter psr_t PS = 0.1;\n"
                       "endpackage\n"
                       "class C #(sr_t CS = 0.1);\n"
                       "endclass\n"
                       "module t #(parameter sr_t P = 0.1);\n"
                       "  initial $display(\"%.12f %0d %.12f %0d %.12f\", P, "
                       "$bits(P), pk::PS, $bits(pk::PS), C#()::CS);\n"
                       "endmodule\n",
                       f),
            "0.100000001490 32 0.100000001490 32 0.100000001490\n");
}

TEST(ValueParameterSimulation,
     RealPackageAndClassParametersOfAnIntegerAreReal) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package pk;\n"
                 "  parameter real PR = 7;\n"
                 "  parameter shortreal PS = 7;\n"
                 "endpackage\n"
                 "class C #(real CR = 7, shortreal CS = 7);\n"
                 "  localparam real LR = 7;\n"
                 "endclass\n"
                 "module t;\n"
                 "  initial $display(\"%g %g %g %g %g\", pk::PR / 2, "
                 "pk::PS / 2, C#()::CR / 2, C#()::CS / 2, C#()::LR / 2);\n"
                 "endmodule\n",
                 f),
      "3.5 3.5 3.5 3.5 3.5\n");
}

TEST(ValueParameterSimulation, RealTypedefModuleParameterIsReal) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef real r_t;\n"
                       "module m #(parameter r_t Q = 2.5);\n"
                       "  parameter r_t R = 7;\n"
                       "  initial $display(\"%g %g %0d\", Q / 2, R / 2, "
                       "$bits(Q));\n"
                       "endmodule\n"
                       "module t;\n"
                       "  m #(.Q(5)) u();\n"
                       "endmodule\n",
                       f),
            "2.5 3.5 64\n");
}

}  // namespace
