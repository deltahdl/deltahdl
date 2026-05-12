#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(TwoStateAndFourState, FourStateToTwoStateXBecomesZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  int dst;\n"
      "  initial begin\n"
      "    src = 8'bxxxx_xxxx;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(TwoStateAndFourState, FourStateToTwoStateZBecomesZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  int dst;\n"
      "  initial begin\n"
      "    src = 8'bzzzz_zzzz;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(TwoStateAndFourState, UnsignedWideningZeroExtends) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [3:0] src;\n"
      "  bit [7:0] dst;\n"
      "  initial begin\n"
      "    src = 4'hA;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 0x0Au);
}

TEST(TwoStateAndFourState, SignedWideningSignExtends) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte src;\n"
      "  int dst;\n"
      "  initial begin\n"
      "    src = -2;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 0xFFFFFFFEu);
}

TEST(TwoStateAndFourState, NarrowingTruncatesMSBs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [7:0] src;\n"
      "  bit [3:0] dst;\n"
      "  initial begin\n"
      "    src = 8'hAB;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 4u);
  EXPECT_EQ(var->value.ToUint64(), 0xBu);
}

TEST(TwoStateAndFourState, FourToTwoStateZeroesOnlyXzBits) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  bit [7:0] dst;\n"
      "  initial begin\n"
      "    src = 8'b1010_x10z;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), 0xA4u);
}

TEST(TwoStateAndFourState, FourStateVariableHoldsXAndZ) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a;\n"
      "  initial a = 4'b1x0z;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("a");
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToString(), "1x0z");
}

TEST(TwoStateAndFourState, IntegerKeepsXzThatIntZeroes) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  int two_state;\n"
      "  integer four_state;\n"
      "  initial begin\n"
      "    src = 8'bxxxxxxxx;\n"
      "    two_state = src;\n"
      "    four_state = src;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* two = f.ctx.FindVariable("two_state");
  auto* four = f.ctx.FindVariable("four_state");
  ASSERT_NE(two, nullptr);
  ASSERT_NE(four, nullptr);
  EXPECT_TRUE(two->value.IsKnown());
  EXPECT_EQ(two->value.ToUint64(), 0u);
  EXPECT_FALSE(four->value.IsKnown());
}

TEST(TwoStateAndFourState, PositiveSignedWideningFillsZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte src;\n"
      "  int dst;\n"
      "  initial begin\n"
      "    src = 8'sd5;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 0x00000005u);
}

TEST(TwoStateAndFourState, LogicAndRegSimulateIdentically) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  reg [7:0] b;\n"
      "  initial begin\n"
      "    a = 8'hCA;\n"
      "    b = 8'hCA;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), vb->value.ToUint64());
  EXPECT_EQ(va->value.width, vb->value.width);
}

// §6.11.2 widening rule applies at any width. A 32-bit signed source with the
// sign bit set, when widened into a 128-bit signed destination, must produce
// sign-extension across the full upper 96 bits — i.e. the multi-word path of
// the conversion code must replicate the MSB through every word above the
// source width.
TEST(TwoStateAndFourState, MultiWordSignedWideningSignExtends) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit signed [31:0]  src;\n"
      "  bit signed [127:0] dst;\n"
      "  initial begin\n"
      "    src = 32'sh80000000;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* dst = f.ctx.FindVariable("dst");
  ASSERT_NE(dst, nullptr);
  EXPECT_EQ(dst->value.width, 128u);
  ASSERT_EQ(dst->value.nwords, 2u);
  // Bits 0..31 hold the original 0x80000000; bits 32..63 sign-extend in the
  // low word; bits 64..127 are entirely sign-extended ones in the high word.
  EXPECT_EQ(dst->value.words[0].aval, 0xFFFFFFFF80000000ull);
  EXPECT_EQ(dst->value.words[1].aval, 0xFFFFFFFFFFFFFFFFull);
}

// §6.11.2 narrowing rule applies at any width. A 128-bit source must
// truncate to a 32-bit destination by keeping only the low 32 bits — the
// upper-word contents must not bleed into the result.
TEST(TwoStateAndFourState, MultiWordNarrowingTruncatesMSBs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [127:0] src;\n"
      "  bit [31:0]  dst;\n"
      "  initial begin\n"
      "    src = 128'hAAAAAAAA_BBBBBBBB_CCCCCCCC_DDDDDDDD;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* dst = f.ctx.FindVariable("dst");
  ASSERT_NE(dst, nullptr);
  EXPECT_EQ(dst->value.width, 32u);
  EXPECT_EQ(dst->value.ToUint64(), 0xDDDDDDDDu);
}

// §6.11.2 4-state→2-state rule applies at any width. A 128-bit 4-state
// source whose high word holds only x/z bits must coerce those bits to zero
// when assigned to a 2-state destination, while preserving the known bits
// from the low word.
TEST(TwoStateAndFourState, MultiWordFourToTwoStateZeroesXz) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [127:0] src;\n"
      "  bit   [127:0] dst;\n"
      "  initial begin\n"
      "    src = {64'hxxxxxxxxxxxxxxxx, 64'hCAFEBABEDEADBEEF};\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* dst = f.ctx.FindVariable("dst");
  ASSERT_NE(dst, nullptr);
  EXPECT_EQ(dst->value.width, 128u);
  ASSERT_EQ(dst->value.nwords, 2u);
  EXPECT_TRUE(dst->value.IsKnown());
  EXPECT_EQ(dst->value.words[0].aval, 0xCAFEBABEDEADBEEFull);
  EXPECT_EQ(dst->value.words[1].aval, 0ull);
}

}  // namespace
