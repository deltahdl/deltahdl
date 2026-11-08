#include <gtest/gtest.h>

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

}  // namespace
