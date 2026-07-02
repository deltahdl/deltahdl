#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

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

  EXPECT_EQ(dst->value.words[0].aval, 0xFFFFFFFF80000000ull);
  EXPECT_EQ(dst->value.words[1].aval, 0xFFFFFFFFFFFFFFFFull);
}

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

// The x/z-to-zero conversion also applies when a 4-state value initializes a
// 2-state variable at declaration, not only in a procedural assignment. Widths
// match here so the numeric-projection path does not mask the coercion.
TEST(TwoStateAndFourState, TwoStateInitializerZeroesXz) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [7:0] a = 8'b1010_x10z;\n"
      "  bit       b = 1'bx;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_TRUE(va->value.IsKnown());
  EXPECT_EQ(va->value.ToUint64(), 0xA4u);
  EXPECT_TRUE(vb->value.IsKnown());
  EXPECT_EQ(vb->value.ToUint64(), 0u);
}

// A 4-state variable keeps the same x/z initializer, discriminating the guard
// against the 2-state coercion above.
TEST(TwoStateAndFourState, FourStateInitializerKeepsXz) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a = 8'b1010_x10z;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* va = f.ctx.FindVariable("a");
  ASSERT_NE(va, nullptr);
  EXPECT_FALSE(va->value.IsKnown());
  EXPECT_EQ(va->value.ToString(), "1010x10z");
}

// reg is one of the four 4-state types, so it retains x and z like logic.
TEST(TwoStateAndFourState, RegHoldsXAndZ) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  reg [3:0] a;\n"
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

// time is the fourth 4-state type; unknown bits survive rather than coercing.
TEST(TwoStateAndFourState, TimeHoldsXAndZ) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  time ts;\n"
      "  initial ts = 64'b1x0z;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("ts");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 64u);
  EXPECT_FALSE(var->value.IsKnown());
}

// A 2-state byte destination forces the incoming unknown/high-Z bits to zero.
TEST(TwoStateAndFourState, ByteConversionZeroesXz) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] src;\n"
      "  byte dst;\n"
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

// Same conversion into a 16-bit 2-state shortint destination.
TEST(TwoStateAndFourState, ShortintConversionZeroesXz) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] src;\n"
      "  shortint dst;\n"
      "  initial begin\n"
      "    src = 16'b0000_0000_1010_x10z;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), 0x00A4u);
}

// Same conversion into a 64-bit 2-state longint destination.
TEST(TwoStateAndFourState, LongintConversionZeroesXz) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [63:0] src;\n"
      "  longint dst;\n"
      "  initial begin\n"
      "    src = 64'b1010_x10z;\n"
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

// The widening direction depends on signedness (§6.11.3): an explicit unsigned
// override on a normally-signed byte zero-extends instead of sign-extending.
// The same 0xFF bits sign-extend to 0xFFFFFFFF when the byte stays signed.
TEST(TwoStateAndFourState, UnsignedByteWideningZeroExtends) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte unsigned src;\n"
      "  int dst;\n"
      "  initial begin\n"
      "    src = 8'hFF;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("dst");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 32u);
  EXPECT_EQ(var->value.ToUint64(), 0x000000FFu);
}

}  // namespace
