#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(SignedAndUnsigned, DefaultSignedScalarsCarriedToSimulator) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte b;\n"
      "  shortint s;\n"
      "  int i;\n"
      "  longint l;\n"
      "  integer ig;\n"
      "  initial begin b = 0; s = 0; i = 0; l = 0; ig = 0; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(f.ctx.FindVariable("b")->is_signed);
  EXPECT_TRUE(f.ctx.FindVariable("s")->is_signed);
  EXPECT_TRUE(f.ctx.FindVariable("i")->is_signed);
  EXPECT_TRUE(f.ctx.FindVariable("l")->is_signed);
  EXPECT_TRUE(f.ctx.FindVariable("ig")->is_signed);
}

TEST(SignedAndUnsigned, DefaultUnsignedScalarsCarriedToSimulator) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  time t0;\n"
      "  bit b0;\n"
      "  logic l0;\n"
      "  reg r0;\n"
      "  initial begin t0 = 0; b0 = 0; l0 = 0; r0 = 0; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.ctx.FindVariable("t0")->is_signed);
  EXPECT_FALSE(f.ctx.FindVariable("b0")->is_signed);
  EXPECT_FALSE(f.ctx.FindVariable("l0")->is_signed);
  EXPECT_FALSE(f.ctx.FindVariable("r0")->is_signed);
}

TEST(SignedAndUnsigned, PackedArraysOfUnsignedTypesAreUnsigned) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit   [7:0]  ba;\n"
      "  logic [15:0] la;\n"
      "  reg   [3:0]  ra;\n"
      "  initial begin ba = 0; la = 0; ra = 0; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.ctx.FindVariable("ba")->is_signed);
  EXPECT_FALSE(f.ctx.FindVariable("la")->is_signed);
  EXPECT_FALSE(f.ctx.FindVariable("ra")->is_signed);
}

TEST(SignedAndUnsigned, ExplicitSignedOverrideObservedAtRuntime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit signed [3:0] src;\n"
      "  int dst;\n"
      "  initial begin\n"
      "    src = 4'b1111;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* src = f.ctx.FindVariable("src");
  auto* dst = f.ctx.FindVariable("dst");
  ASSERT_NE(src, nullptr);
  ASSERT_NE(dst, nullptr);
  EXPECT_TRUE(src->is_signed);
  EXPECT_EQ(dst->value.width, 32u);
  EXPECT_EQ(dst->value.ToUint64(), 0xFFFFFFFFu);
}

TEST(SignedAndUnsigned, ExplicitUnsignedOverrideObservedAtRuntime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int unsigned src;\n"
      "  longint dst;\n"
      "  initial begin\n"
      "    src = 32'hFFFFFFFF;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* src = f.ctx.FindVariable("src");
  auto* dst = f.ctx.FindVariable("dst");
  ASSERT_NE(src, nullptr);
  ASSERT_NE(dst, nullptr);
  EXPECT_FALSE(src->is_signed);
  EXPECT_EQ(dst->value.width, 64u);
  EXPECT_EQ(dst->value.ToUint64(), 0x00000000FFFFFFFFull);
}

}  // namespace
