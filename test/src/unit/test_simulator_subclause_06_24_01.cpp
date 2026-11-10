#include <gtest/gtest.h>

#include <format>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(CastOperatorSim, IntCastFromReal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int x;\n"
      "  initial x = int'(4.0);\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

TEST(CastOperatorSim, SizeCastPadsNarrowToWide) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  initial result = int'(8'hAB);\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(CastOperatorSim, SizeCastSameWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int x;\n"
      "  int result;\n"
      "  initial begin\n"
      "    x = 32'h12345678;\n"
      "    result = int'(x);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x12345678u);
}

TEST(CastOperatorSim, LongintCastPads) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  longint result;\n"
      "  initial result = longint'(32'hDEADBEEF);\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xDEADBEEFu);
}

TEST(CastOperatorSim, VoidCastDiscardsValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int x;\n"
      "  function int next(); return x + 1; endfunction\n"
      "  initial begin\n"
      "    x = 42;\n"
      "    void'(next());\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(CastOperatorSim, ConstCastPreservesValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int result;\n"
      "  initial result = const'(99);\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(CastOperatorSim, UnsignedCastOfNegativeFour) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] regA;\n"
      "  initial regA = unsigned'(-4);\n"
      "endmodule\n",
      f, "regA");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFCu);
}

TEST(CastOperatorSim, SignedCastOfFourBitVector) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic signed [7:0] regS;\n"
      "  initial regS = signed'(4'b1100);\n"
      "endmodule\n",
      f, "regS");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFCu);
}

TEST(CastOperatorSim, NumericSizeCastTruncates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] r;\n"
      "  initial r = 4'(8'hAB);\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xBu);
}

TEST(CastOperatorSim, NumericSizeCastParameterWidthTruncates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  parameter N = 4;\n"
      "  logic [7:0] r;\n"
      "  initial r = N'(8'hAB);\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xBu);
}

TEST(CastOperatorSim, NumericSizeCastSignExtendsSignedOperand) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic signed [3:0] s;\n"
      "  logic [7:0] r;\n"
      "  initial begin\n"
      "    s = 4'sb1100;\n"
      "    r = 8'(s);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFCu);
}

TEST(CastOperatorSim, NumericSizeCastZeroExtendsUnsignedOperand) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] u;\n"
      "  logic [7:0] r;\n"
      "  initial begin\n"
      "    u = 4'b1111;\n"
      "    r = 8'(u);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

TEST(CastOperatorSim, NumericSizeCastLocalparamWidthTruncates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  localparam N = 4;\n"
      "  logic [7:0] r;\n"
      "  initial r = N'(8'hAB);\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xBu);
}

TEST(CastOperatorSim, IntCastFromRealRoundsHalfUp) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int result;\n"
      "  initial result = int'(2.5);\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(CastOperatorSim, SigningCastFoldsInLocalparamInitializer) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  localparam signed [7:0] P = signed'(4'b1100);\n"
      "  logic signed [7:0] r;\n"
      "  initial r = P;\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFCu);
}

TEST(CastOperatorSim, SizeCastFoldsInLocalparamInitializer) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  localparam [7:0] P = 8'(4'b1100);\n"
      "  logic [7:0] r;\n"
      "  initial r = P;\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x0Cu);
}

TEST(CastOperatorSim, CastDestinationWakesAnEventControlOnIt) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int v;\n"
      "  integer hits;\n"
      "  always @(v) hits = hits + 1;\n"
      "  initial begin\n"
      "    hits = 0;\n"
      "    #1 $cast(v, 7);\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(CastOperatorSim, IntegerCastToShortrealIsItsValueInSinglePrecision) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  shortreal s;\n"
                       "  byte c = -5;\n"
                       "  initial begin\n"
                       "    s = shortreal'(2);\n"
                       "    $display(\"%f %f %f %f\", s, shortreal'(-3),\n"
                       "             shortreal'(c), real'(c));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "2.000000 -3.000000 -5.000000 -5.000000\n");
}

TEST(CastOperatorSim, CastToA4StateTypeKeepsXAndZ) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef logic [7:0] l8_t;\n"
                       "  logic [3:0] l;\n"
                       "  initial begin\n"
                       "    l = 4'b1x0z;\n"
                       "    $display(\"%b %b %b\", integer'(l), l8_t'(l),\n"
                       "             integer'(4'bx));\n"
                       "    $display(\"%b %b %0d\", logic'(1'bx), int'(l),\n"
                       "             $bits(time'(l)));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "00000000000000000000000000001x0z 00001x0z "
            "0000000000000000000000000000xxxx\n"
            "x 00000000000000000000000000001000 64\n");
}

TEST(CastOperatorSim, CastToASignedTypeIsSigned) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic [7:0] regA, regB;\n"
                       "  int r;\n"
                       "  initial begin\n"
                       "    regA = 8'h80; regB = 8'h01;\n"
                       "    r = byte'(regA) + byte'(regB);\n"
                       "    $display(\"%0d %0d %0d\", r, int'(1) - 4,\n"
                       "             byte'(8'h80) + 0);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "-127 -3 -128\n");
}

TEST(CastOperatorSim, SizeCastIsItsOperandsContextWidth) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic [3:0] x = 4'hF;\n"
                       "  logic [5:0] y = 6'hA;\n"
                       "  let mult(a, b) = ($bits(a) + $bits(b))'(a * b);\n"
                       "  initial $display(\"%0d %0d %0d\", 10'(x * y),\n"
                       "                   ($bits(x) + $bits(y))'(x * y),\n"
                       "                   mult(x, y));\n"
                       "endmodule\n",
                       f),
            "150 150 150\n");
}

TEST(CastOperatorSim, CastToAClassOrPackageTypedef) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p; typedef shortint S; endpackage\n"
                       "module t;\n"
                       "  class C;\n"
                       "    typedef byte T;\n"
                       "    static function int narrow(int v);\n"
                       "      return T'(v);\n"
                       "    endfunction\n"
                       "  endclass\n"
                       "  initial $display(\"%0d %0d %0d\", C::T'(261),\n"
                       "                   C::narrow(261), p::S'(70000));\n"
                       "endmodule\n",
                       f),
            "5 5 4464\n");
}

TEST(CastOperatorSim, SizeSigningAndConstCastsHaveTheTypesTheClauseGives) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module t;\n"
          "  logic [7:0] x;\n"
          "  bit [7:0] b;\n"
          "  logic signed [3:0] s;\n"
          "  initial $display(\"%0d%0d%0d%0d %0d%0d%0d %0d%0d %0d%0d%0d\",\n"
          "    type(4'(b)) == type(bit [3:0]),\n"
          "    type(4'(x)) == type(logic [3:0]),\n"
          "    type(8'(s)) == type(logic signed [7:0]),\n"
          "    type(4'(b)) == type(logic [3:0]),\n"
          "    type(signed'(b)) == type(bit signed [7:0]),\n"
          "    type(signed'(x)) == type(logic signed [7:0]),\n"
          "    type(unsigned'(s)) == type(logic [3:0]),\n"
          "    type(const'(b)) == type(bit [7:0]),\n"
          "    type(const'(s)) == type(logic signed [3:0]),\n"
          "    $bits(signed'(b)), $bits(const'(s)), $bits((5+2)'(b)));\n"
          "endmodule\n",
          f),
      "1110 111 11 847\n");
}

TEST(CastOperatorSim, ConstantPrimarySizeCastPadsAndTruncates) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  parameter P = 17;\n"
                 "  parameter Q = 16;\n"
                 "  logic [7:0] x = 8'hF7;\n"
                 "  logic signed [3:0] s = 4'b1001;\n"
                 "  initial $display(\"%h %h %h %0d %0d\", 17'(x - 2),\n"
                 "                   P'(x - 2), (Q+1)'(x - 2), (Q-13)'(x),\n"
                 "                   8'(s));\n"
                 "endmodule\n",
                 f),
      "000f5 000f5 000f5 7 -7\n");
}

TEST(CastOperatorSim, ShortrealCastToIntRounds) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  shortreal a = 2.5, b = -2.5, c = 1.25;\n"
                       "  int i;\n"
                       "  initial begin\n"
                       "    i = c;\n"
                       "    $display(\"%0d %0d %0d %0d\", int'(a), int'(b),\n"
                       "             int'(c), i);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "3 -3 1 1\n");
}

TEST(CastOperatorSim, StringAndSignedCastsMatchTheirSystemFunctions) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  bit [7:0] b = 8'h85;\n"
                       "  logic [3:0] l = 4'b1100;\n"
                       "  string s;\n"
                       "  initial begin\n"
                       "    s = string'(16'h4142);\n"
                       "    $display(\"%s %0d %0d %0d %0d\", s, signed'(b),\n"
                       "             $signed(b) === signed'(b),\n"
                       "             $unsigned(l) === unsigned'(l),\n"
                       "             signed'(l));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "AB -123 1 1 -4\n");
}

TEST(CastOperatorSim, ExplicitCastsSumAsTheirTemporariesDo) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef bit [3:0] cast_t1;\n"
                       "typedef byte cast_t2;\n"
                       "module t;\n"
                       "  int expr_1 = 'h1F, expr_2 = 'h1FF;\n"
                       "  int A, B;\n"
                       "  cast_t1 temp1;\n"
                       "  cast_t2 temp2;\n"
                       "  initial begin\n"
                       "    A = cast_t1'(expr_1) + cast_t2'(expr_2);\n"
                       "    temp1 = expr_1;\n"
                       "    temp2 = expr_2;\n"
                       "    B = temp1 + temp2;\n"
                       "    $display(\"%0d %0d\", A, B);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "270 270\n");
}

struct RoundTrip {
  std::string_view msb;
  std::string_view source;
  std::string_view from_bits;
  std::string_view from_logic;
};

std::string StructureRoundTrip(const RoundTrip& r, std::string_view k_value) {
  return std::format(
      "typedef struct {{ bit f; int i; logic [2:0] k; }} st;\n"
      "typedef bit [{0} : 0] stbits;\n"
      "typedef logic [{0} : 0] stlogic;\n"
      "module t;\n"
      "  st a [7:0];\n"
      "  st s, sb, sl;\n"
      "  stbits b;\n"
      "  stlogic l;\n"
      "  initial begin\n"
      "    {1} = '{{1'b1, 32'h12345678, {4}}};\n"
      "    b = stbits'({1});\n"
      "    l = stlogic'({1});\n"
      "    {2} = st'(b);\n"
      "    {3} = st'(l);\n"
      "    $display(\"%0d %h %b %0d %h %b %b\", $bits(stbits), b, l[2:0],\n"
      "             {2}.f, {2}.i, {2}.k, {3}.k);\n"
      "  end\n"
      "endmodule\n",
      r.msb, r.source, r.from_bits, r.from_logic, k_value);
}

constexpr RoundTrip kThroughVariables = {"35", "s", "sb", "sl"};
constexpr RoundTrip kThroughElements = {"35", "a[3]", "a[4]", "a[5]"};

TEST(CastOperatorSim, UnpackedStructureConvertsToBitsAndBack) {
  for (const RoundTrip& r : {kThroughVariables, kThroughElements}) {
    SCOPED_TRACE(r.source);
    SimFixture f;
    EXPECT_EQ(RunCapture(StructureRoundTrip(r, "3'b110"), f),
              "36 891a2b3c6 110 1 12345678 110 110\n");
  }
}

TEST(CastOperatorSim, UnknownBitsOfAStructureSurviveOnlyALogicCast) {
  SimFixture f;
  EXPECT_EQ(RunCapture(StructureRoundTrip(kThroughVariables, "3'b1x0"), f),
            "36 891a2b3c4 1x0 1 12345678 100 1x0\n");
}

TEST(CastOperatorSim,
     DISABLED_UnknownBitsOfAnArrayElementStructureSurviveALogicCast) {
  SimFixture f;
  EXPECT_EQ(RunCapture(StructureRoundTrip(kThroughElements, "3'b1x0"), f),
            "36 891a2b3c4 1x0 1 12345678 100 1x0\n");
}

TEST(CastOperatorSim, DISABLED_StructureConvertsThroughATypeSizedByItsBits) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          StructureRoundTrip({"$bits(st) - 1", "s", "sb", "sl"}, "3'b1x0"), f),
      "36 891a2b3c4 1x0 1 12345678 100 1x0\n");
}

TEST(CastOperatorSim, DISABLED_TypeParameterCastTakesEachInstancesType) {
  SimFixture f;
  const std::string kModule =
      "module sub #(type T = int);\n"
      "  logic [8:0] x = 9'h1FF;\n"
      "  int v;\n"
      "  initial begin\n"
      "    v = T'(x);\n"
      "    #1 $display(\"%m %0d\", v);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(
      RunCapture(kModule + "module t; sub #(byte) a(); sub #(logic [3:0]) b();"
                           " sub #(shortint) c(); endmodule\n",
                 f),
      "t.a -1\nt.b 15\nt.c 511\n");
  SimFixture g;
  EXPECT_EQ(
      RunCapture(kModule + "module t; sub #(shortint) c(); sub #(logic [3:0]) "
                           "b(); sub #(byte) a(); endmodule\n",
                 g),
      "t.c 511\nt.b 15\nt.a -1\n");
}

}  // namespace
