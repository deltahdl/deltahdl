#include "fixture_real.h"
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(RealConversion, CastRealToInt_NegRound) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  int result;\n"
      "  initial begin\n"
      "    r = -1.5;\n"
      "    result = int'(r);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  auto neg2_32bit = static_cast<uint32_t>(-2);
  EXPECT_EQ(var->value.ToUint64(), neg2_32bit);
}

TEST(RealConversion, CastRealToInt_LrmExamples) {
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

TEST(RealConversion, ImplicitRealToInt_Rounds) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  real r;\n"
      "  int result;\n"
      "  initial begin\n"
      "    r = 1.5;\n"
      "    result = r;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(RealConversion, ImplicitIntToReal) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int i;\n"
      "  real r;\n"
      "  initial begin\n"
      "    i = 42;\n"
      "    r = i;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_NEAR(VecToDouble(var->value), 42.0, 1e-10);
}

TEST(RealConversion, XzBecomesZeroInRealConversion) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] val;\n"
      "  real r;\n"
      "  initial begin\n"
      "    r = val;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_NEAR(VecToDouble(var->value), 0.0, 1e-10);
}

// Per-bit form of the x/z rule: the known bits of a partly-unknown vector must
// survive the conversion to real while only the x bits collapse to zero. With
// the high nibble known (1010) and the low nibble x, the result is 0xA0 = 160.
TEST(RealConversion, KnownBitsSurviveWhileXBitsZeroOnRealConversion) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] val;\n"
      "  real r;\n"
      "  initial begin\n"
      "    val = 8'b1010xxxx;\n"
      "    r = val;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_NEAR(VecToDouble(var->value), 160.0, 1e-10);
}

// The rule names both x and z; exercise the high-impedance half explicitly.
// High nibble known (1010), low nibble z -> 0xA0 = 160.
TEST(RealConversion, HighZBitsBecomeZeroOnRealConversion) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] val;\n"
      "  real r;\n"
      "  initial begin\n"
      "    val = 8'b1010zzzz;\n"
      "    r = val;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("r");
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

}  // namespace
