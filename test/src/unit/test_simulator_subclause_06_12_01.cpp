#include <gtest/gtest.h>

#include <cstdint>

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

// Per-bit form of the x/z rule: the known bits of a partly-unknown vector must
// survive the conversion to real while only the x bits collapse to zero. With
// the high nibble known (1010) and the low nibble x, the result is 0xA0 = 160.
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

// The rule names both x and z; exercise the high-impedance half explicitly.
// High nibble known (1010), low nibble z -> 0xA0 = 160.
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

// Round-to-nearest must hold for negative non-tie magnitudes too, not just the
// exact-half tie: -2.7 rounds to -3 and -2.2 rounds to -2 on implicit assign.
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

// A declaration initializer is an assignment, so a real initializer of an
// integer variable rounds to the nearest integer rather than reinterpreting the
// raw double bits. int'(truncate) or a bit copy would not yield 36 here.
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

// Ties-away-from-zero must hold on the declaration-initializer path too, in
// both sign directions: 35.5 -> 36, 1.5 -> 2, -1.5 -> -2.
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

// The reverse direction on the declaration-initializer path: an integer
// initializer of a real variable is converted numerically, so the stored value
// is the double 5.0 (its bit pattern), not the raw integer bits.
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

// x/z bits read as zero on the declaration-initializer conversion to real while
// the known bits survive: high nibble 1010, low nibble x -> 0xA0 = 160.0.
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

// A nonblocking assignment is an assignment too, so the conversion applies at
// that distinct syntactic position (a separate scheduling call site from the
// blocking and declaration-initializer paths). real->int rounds with a tie away
// from zero (2.5 -> 3, discriminating round-half-to-even's 2), and int->real
// converts numerically (7 -> 7.0).
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

// shortreal is one of the real variable types (§6.12), so the round-to-nearest
// conversion applies to it as well; the value travels the 32-bit-float branch
// of the real read path. 2.5 is exact in float and ties to 3.
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

// realtime is synonymous with real (§6.12), so it is likewise converted by
// rounding; 1.5 ties to 2.
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

// The conversion target may be any integer type (§6.11), not just int. Rounding
// into a 64-bit longint exercises the full-width target path; 35.5 ties to 36.
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

// DeclInitIntToReal above is a declaration at module scope, which the lowerer
// initializes. A declaration written inside a procedural block is initialized
// by ExecVarDeclImpl in statement_assign_decl.cpp instead, and §6.12.1's
// conversion has to reach it there too: a plain resize of the initializer to
// the variable's 64 bits would store the integer 5's bit pattern, which read as
// a double is 2.47e-323 rather than 5.0. The block-local cannot be found once
// the block has ended, so the value is carried out through a module-level real.
TEST(RealConversion, BlockDeclInitIntToReal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  real out;\n"
      "  initial begin\n"
      "    real r = 5;\n"
      "    out = r;\n"
      "  end\n"
      "endmodule\n",
      f, "out");
  ASSERT_NE(var, nullptr);
  EXPECT_NEAR(VecToDouble(var->value), 5.0, 1e-10);
}

// §10.8 makes passing a value to a subroutine argument an assignment-like
// context, so §6.12.1's rounding reaches a real actual passed to an int
// formal: `fi(12.5)` reads 13.
// The value's 64-bit pattern resized to the formal's 32 read 0.
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

// The same through a real variable rather than a literal.
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

// §6.12.1 rounds a half away from zero, so -3.5 into a shortint formal is the
// 16-bit -4, fffc.
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

// A longint formal is as wide as the real's pattern, so no resize stood
// between them and the pattern itself was the formal's value.
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

// -3.5 into a byte formal is the 8-bit -4, fc.
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

// §8.7 binds a constructor's actuals as any subroutine's, so `new(6.5)` into
// `input int v` stores 7.
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
      "    C c = new(6.5);\n"
      "    a = c.r;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 7u);
}

// A class method's formal takes the same conversion: `c.m(12.5)` returns 13.
TEST(RealConversion, RealActualRoundsIntoAClassMethodIntFormal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  class C;\n"
      "    function int m(input int x); return x; endfunction\n"
      "  endclass\n"
      "  int a;\n"
      "  initial begin\n"
      "    C c = new;\n"
      "    a = c.m(12.5);\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 13u);
}

}  // namespace
