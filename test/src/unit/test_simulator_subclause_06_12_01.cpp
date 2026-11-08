#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_real.h"
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(RealConversion, CastRealToIntNegativeTieRoundsAway) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  real r;\n"
      "  int result;\n"
      "  initial begin\n"
      "    r = -1.5;\n"
      "    result = int'(r);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  auto neg2_32bit = static_cast<uint32_t>(-2);
  EXPECT_EQ(var->value.ToUint64(), neg2_32bit);
}

TEST(RealConversion, CastRealToIntRoundsToNearestTiesAway) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real r1, r2, r3;\n"
      "  int a, b, c;\n"
      "  initial begin\n"
      "    r1 = 35.7; a = int'(r1);\n"
      "    r2 = 35.5; b = int'(r2);\n"
      "    r3 = 35.2; c = int'(r3);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 36u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 36u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 35u);
}

TEST(RealConversion, ImplicitRealToIntRoundsToNearest) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  real r;\n"
      "  int result;\n"
      "  initial begin\n"
      "    r = 1.5;\n"
      "    result = r;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(RealConversion, ImplicitIntToReal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int i;\n"
      "  real r;\n"
      "  initial begin\n"
      "    i = 42;\n"
      "    r = i;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_NEAR(VecToDouble(var->value), 42.0, 1e-10);
}

TEST(RealConversion, KnownBitsSurviveWhileXBitsZeroOnRealConversion) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] val;\n"
      "  real r;\n"
      "  initial begin\n"
      "    val = 8'b1010xxxx;\n"
      "    r = val;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_NEAR(VecToDouble(var->value), 160.0, 1e-10);
}

TEST(RealConversion, HighZBitsBecomeZeroOnRealConversion) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] val;\n"
      "  real r;\n"
      "  initial begin\n"
      "    val = 8'b1010zzzz;\n"
      "    r = val;\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_NEAR(VecToDouble(var->value), 160.0, 1e-10);
}

TEST(RealConversion, ImplicitNegativeNonTieRoundsToNearest) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real r1, r2;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    r1 = -2.7; a = r1;\n"
      "    r2 = -2.2; b = r2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(),
            static_cast<uint32_t>(-3));
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(),
            static_cast<uint32_t>(-2));
}

TEST(RealConversion, DeclInitRealToIntRoundsNotTruncates) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int i = 35.7;\n"
      "endmodule\n",
      f, "i");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 36u);
}

TEST(RealConversion, DeclInitRealToIntTiesAwayFromZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a = 35.5;\n"
      "  int b = 1.5;\n"
      "  int c = -1.5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 36u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(),
            static_cast<uint32_t>(-2));
}

TEST(RealConversion, DeclInitIntToReal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  real r = 5;\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_NEAR(VecToDouble(var->value), 5.0, 1e-10);
}

TEST(RealConversion, DeclInitXzBitsBecomeZeroOnRealConversion) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  real r = 8'b1010xxxx;\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_NEAR(VecToDouble(var->value), 160.0, 1e-10);
}

TEST(RealConversion, NonblockingAssignConvertsBothDirections) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  int i;\n"
      "  int j;\n"
      "  real s;\n"
      "  initial begin\n"
      "    r = 2.5;\n"
      "    i <= r;\n"
      "    j = 7;\n"
      "    s <= j;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("i")->value.ToUint64(), 3u);
  EXPECT_NEAR(VecToDouble(f.ctx.FindVariable("s")->value), 7.0, 1e-10);
}

TEST(RealConversion, ShortRealToIntRoundsToNearest) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  shortreal sr;\n"
      "  int i;\n"
      "  initial begin\n"
      "    sr = 2.5;\n"
      "    i = sr;\n"
      "  end\n"
      "endmodule\n",
      f, "i");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(RealConversion, RealtimeToIntRoundsToNearest) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  realtime rt;\n"
      "  int i;\n"
      "  initial begin\n"
      "    rt = 1.5;\n"
      "    i = rt;\n"
      "  end\n"
      "endmodule\n",
      f, "i");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(RealConversion, RealToLongintRoundsToNearest) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  real r;\n"
      "  longint l;\n"
      "  initial begin\n"
      "    r = 35.5;\n"
      "    l = r;\n"
      "  end\n"
      "endmodule\n",
      f, "l");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 36u);
}

TEST(RealConversion, BlockDeclInitIntToReal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  real out;\n"
      "  initial begin\n"
      "    static real r = 5;\n"
      "    out = r;\n"
      "  end\n"
      "endmodule\n",
      f, "out");
  ASSERT_NE(var, nullptr);
  EXPECT_NEAR(VecToDouble(var->value), 5.0, 1e-10);
}

TEST(RealConversion, RealActualRoundsIntoAnIntFormal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  function int fi(input int x); return x; endfunction\n"
      "  int a;\n"
      "  initial a = fi(12.5);\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 13u);
}

TEST(RealConversion, RealVariableActualRoundsIntoAnIntFormal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  function int fi(input int x); return x; endfunction\n"
      "  real r = 12.5;\n"
      "  int a;\n"
      "  initial a = fi(r);\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 13u);
}

TEST(RealConversion, NegativeRealActualRoundsAwayIntoAShortintFormal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  function shortint fs(input shortint x); return x; endfunction\n"
      "  shortint a;\n"
      "  initial a = fs(-3.5);\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFFCu);
}

TEST(RealConversion, RealActualRoundsIntoALongintFormal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  function longint fl(input longint x); return x; endfunction\n"
      "  longint a;\n"
      "  initial a = fl(12.5);\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 13u);
}

TEST(RealConversion, NegativeRealActualRoundsAwayIntoAByteFormal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  function byte fb(input byte x); return x; endfunction\n"
      "  byte a;\n"
      "  initial a = fb(-3.5);\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFCu);
}

TEST(RealConversion, RealActualRoundsIntoAConstructorIntFormal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class C;\n"
      "    int r;\n"
      "    function new(input int v); r = v; endfunction\n"
      "  endclass\n"
      "  int a;\n"
      "  initial begin\n"
      "    static C c = new(6.5);\n"
      "    a = c.r;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

TEST(RealConversion, RealActualRoundsIntoAClassMethodIntFormal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class C;\n"
      "    function int m(input int x); return x; endfunction\n"
      "  endclass\n"
      "  int a;\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    a = c.m(12.5);\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 13u);
}

TEST(RealConversion, StaticPropertyRealInitializerRoundsIntoAnInt) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class C;\n"
      "    static int t = 3.6;\n"
      "  endclass\n"
      "  int a;\n"
      "  initial a = C::t;\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

TEST(RealConversion, StaticPropertyNegativeRealInitializerRoundsAway) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class C;\n"
      "    static int u = -2.5;\n"
      "  endclass\n"
      "  int a;\n"
      "  initial a = C::u;\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), static_cast<uint32_t>(-3));
}

TEST(RealConversionSim, AssignmentToAnArrayElementConverts) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  real rv = 2.0;\n"
                       "  logic signed [3:0] s = -1;\n"
                       "  logic [7:0] r [1:2];\n"
                       "  logic [7:0] x;\n"
                       "  real ra [2];\n"
                       "  initial begin\n"
                       "    r[1] = rv + s;\n"
                       "    r[2] = 2.6;\n"
                       "    x = rv + s;\n"
                       "    ra[0] = 3;\n"
                       "    ra[1] = 1.25;\n"
                       "    $display(\"%h %h %h %0.2f %0.2f\", r[1], r[2], x,\n"
                       "             ra[0], ra[1]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "01 03 01 3.00 1.25\n");
}

}  // namespace
