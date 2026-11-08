#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

static bool RunSim(SimFixture& f, const std::string& src) {
  auto* design = ElaborateSrc(src, f);
  if (!design) return false;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  return true;
}

TEST(IntegerLiteralSim, UnbasedUnsizedZeroClearsByte) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = '0;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(IntegerLiteralSim, HexLiteralDistinctNibbles) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'hA5;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xA5u);
}

TEST(IntegerLiteralSim, BinaryNumber) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'b10101010;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAAu);
}

TEST(IntegerLiteralSim, HexNumber) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'hFF;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

TEST(IntegerLiteralSim, DecimalSizedBase) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd200;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 200u);
}

TEST(IntegerLiteralSim, DecimalZDigitAllBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'dz;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);

  EXPECT_NE(var->value.words[0].bval, 0u);
}

TEST(IntegerLiteralSim, Size16Bit) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial x = 16'hBEEF;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xBEEFu);
}

TEST(IntegerLiteralSim, UnsignedNumberUnderscores) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int x;\n"
      "  initial x = 1_000;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1000u);
}

TEST(IntegerLiteralSim, BinaryValueUnderscores) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'b1010_1010;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAAu);
}

TEST(IntegerLiteralSim, DecimalBaseUpper) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'D99;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(IntegerLiteralSim, BinaryBaseUpper) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] x;\n"
      "  initial x = 4'B1111;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFu);
}

TEST(IntegerLiteralSim, OctalBaseUpper) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'O77;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 077u);
}

TEST(IntegerLiteralSim, HexBaseUpper) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'HAB;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(IntegerLiteralSim, SignedDecimal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'sd99;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(IntegerLiteralSim, SignedBinary) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] x;\n"
      "  initial x = 4'sb1010;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAu);
}

TEST(IntegerLiteralSim, SignedHex) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'shAB;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(IntegerLiteralSim, XDigitInHex) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'h0x;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);

  uint64_t aval = var->value.words[0].aval;
  uint64_t bval = var->value.words[0].bval;
  EXPECT_EQ(aval & 0xFu, 0xFu);
  EXPECT_EQ(bval & 0xFu, 0xFu);
}

TEST(IntegerLiteralSim, ZDigitInHex) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'h0z;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);

  uint64_t aval = var->value.words[0].aval;
  uint64_t bval = var->value.words[0].bval;
  EXPECT_EQ(aval & 0xFu, 0x0u);
  EXPECT_EQ(bval & 0xFu, 0xFu);
}

TEST(IntegerLiteralSim, QuestionMarkAsZ) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] x;\n"
      "  initial x = 4'b0?0?;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);

  uint64_t bval = var->value.words[0].bval;
  EXPECT_NE(bval & 0x5u, 0u);
}

TEST(IntegerLiteralSim, UnbasedUnsizedOne) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = '1;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64() & 0xFFu, 0xFFu);
}

TEST(IntegerLiteralSim, UnbasedUnsizedX) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 'x;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);

  EXPECT_NE(var->value.words[0].aval, 0u);
  EXPECT_NE(var->value.words[0].bval, 0u);
}

TEST(IntegerLiteralSim, UnbasedUnsizedZ) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 'z;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);

  EXPECT_NE(var->value.words[0].bval, 0u);
}

TEST(IntegerLiteralSim, HexDigitUppercase) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [23:0] x;\n"
      "  initial x = 24'hABCDEF;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xABCDEFu);
}

TEST(IntegerLiteralSim, AllBasesProduceSameValue) {
  SimFixture f;
  ASSERT_TRUE(RunSim(f,
                     "module t;\n"
                     "  logic [7:0] a, b, c, d;\n"
                     "  initial begin\n"
                     "    a = 255;\n"
                     "    b = 8'hFF;\n"
                     "    c = 8'o377;\n"
                     "    d = 8'b1111_1111;\n"
                     "  end\n"
                     "endmodule\n"));
  const char* const kNames[] = {"a", "b", "c", "d"};
  for (const char* name : kNames) {
    auto* v = f.ctx.FindVariable(name);
    ASSERT_NE(v, nullptr) << name;
    EXPECT_EQ(v->value.ToUint64(), 255u) << name;
  }
}

TEST(IntegerLiteralSim, OctalZDigitFillsThreeBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [5:0] x;\n"
      "  initial x = 6'o0z;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 0x07, 0x00u);
  EXPECT_EQ(var->value.words[0].bval & 0x07, 0x07u);
}

TEST(IntegerLiteralSim, BinaryZDigitFillsOneBit) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] x;\n"
      "  initial x = 4'b010z;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 0x1, 0x0u);
  EXPECT_EQ(var->value.words[0].bval & 0x1, 0x1u);
}

TEST(IntegerLiteralSim, SignedOctal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'so77;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 077u);
}

TEST(IntegerLiteralSim, XDigitInBinary) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] x;\n"
      "  initial x = 4'b1x01;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 0x4, 0x4u);
  EXPECT_EQ(var->value.words[0].bval & 0x4, 0x4u);
}

TEST(IntegerLiteralSim, XDigitInOctal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [5:0] x;\n"
      "  initial x = 6'o0x;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 0x07, 0x07u);
  EXPECT_EQ(var->value.words[0].bval & 0x07, 0x07u);
}

TEST(IntegerLiteralSim, DecimalXDigitFillsAllBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'dx;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  uint8_t mask = 0xFF;
  EXPECT_EQ(var->value.words[0].bval & mask, mask);
}

TEST(IntegerLiteralSim, OctalLiteralValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'o77;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 63u);
}

TEST(IntegerLiteralSim, UnsizedHexXExtendsToWideContext) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [63:0] x;\n"
      "  initial x = 'hx;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval, ~uint64_t{0});
  EXPECT_EQ(var->value.words[0].bval, ~uint64_t{0});
}

TEST(IntegerLiteralSim, UnsizedHexZExtendsToWideContext) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [63:0] x;\n"
      "  initial x = 'hz;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval, uint64_t{0});
  EXPECT_EQ(var->value.words[0].bval, ~uint64_t{0});
}

TEST(IntegerLiteralSim, QuestionMarkFillsFourBitsInHex) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'h5?;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 0xF0u, 0x50u);
  EXPECT_EQ(var->value.words[0].bval & 0x0Fu, 0x0Fu);
  EXPECT_EQ(var->value.words[0].bval & 0xF0u, 0x00u);
}

TEST(IntegerLiteralSim, QuestionMarkFillsThreeBitsInOctal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [5:0] x;\n"
      "  initial x = 6'o7?;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 0x38u, 0x38u);
  EXPECT_EQ(var->value.words[0].bval & 0x07u, 0x07u);
  EXPECT_EQ(var->value.words[0].bval & 0x38u, 0x00u);
}

TEST(IntegerLiteralSim, LiteralOccupiesLogicVectorMsbFirst) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  logic [3:0] hi;\n"
      "  logic [3:0] lo;\n"
      "  initial begin\n"
      "    v = 8'hA5;\n"
      "    hi = v[7:4];\n"
      "    lo = v[3:0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* hi = f.ctx.FindVariable("hi");
  auto* lo = f.ctx.FindVariable("lo");
  ASSERT_NE(hi, nullptr);
  ASSERT_NE(lo, nullptr);
  EXPECT_EQ(hi->value.ToUint64(), 0xAu);
  EXPECT_EQ(lo->value.ToUint64(), 0x5u);
}

TEST(IntegerLiteralSim, WideDecimalLiteralSetsBitEighty) {
  SimFixture f;
  ASSERT_TRUE(RunSim(f,
                     "module t;\n"
                     "  logic [80:0] x;\n"
                     "  logic [16:0] hi;\n"
                     "  logic [63:0] lo;\n"
                     "  initial begin\n"
                     "    x = 81'd1208925819614629174706177;\n"
                     "    hi = x[80:64];\n"
                     "    lo = x[63:0];\n"
                     "  end\n"
                     "endmodule\n"));
  auto* hi = f.ctx.FindVariable("hi");
  auto* lo = f.ctx.FindVariable("lo");
  ASSERT_NE(hi, nullptr);
  ASSERT_NE(lo, nullptr);
  EXPECT_EQ(hi->value.ToUint64(), 0x10000u);
  EXPECT_EQ(lo->value.ToUint64(), 1u);
}

TEST(IntegerLiteralSim, UnsizedDecimalPastSixtyFourBitsKeepsItsValue) {
  SimFixture f;
  ASSERT_TRUE(RunSim(f,
                     "module t;\n"
                     "  logic [95:0] y;\n"
                     "  logic [31:0] hi;\n"
                     "  logic [63:0] lo;\n"
                     "  initial begin\n"
                     "    y = 1180591620717411303424;\n"
                     "    hi = y[95:64];\n"
                     "    lo = y[63:0];\n"
                     "  end\n"
                     "endmodule\n"));
  auto* hi = f.ctx.FindVariable("hi");
  auto* lo = f.ctx.FindVariable("lo");
  ASSERT_NE(hi, nullptr);
  ASSERT_NE(lo, nullptr);
  EXPECT_EQ(hi->value.ToUint64(), 0x40u);
  EXPECT_EQ(lo->value.ToUint64(), 0u);
}

TEST(IntegerLiteralSim, WideDecimalLiteralPadsSmallValueWithZeros) {
  SimFixture f;
  ASSERT_TRUE(RunSim(f,
                     "module t;\n"
                     "  logic [79:0] x, z;\n"
                     "  logic [15:0] xhi, zhi;\n"
                     "  logic [63:0] xlo, zlo;\n"
                     "  initial begin\n"
                     "    x = 80'd4_294_967_296;\n"
                     "    z = 80'd0;\n"
                     "    xhi = x[79:64];\n"
                     "    xlo = x[63:0];\n"
                     "    zhi = z[79:64];\n"
                     "    zlo = z[63:0];\n"
                     "  end\n"
                     "endmodule\n"));
  auto* xhi = f.ctx.FindVariable("xhi");
  auto* xlo = f.ctx.FindVariable("xlo");
  auto* zhi = f.ctx.FindVariable("zhi");
  auto* zlo = f.ctx.FindVariable("zlo");
  ASSERT_NE(xhi, nullptr);
  ASSERT_NE(xlo, nullptr);
  ASSERT_NE(zhi, nullptr);
  ASSERT_NE(zlo, nullptr);
  EXPECT_EQ(xhi->value.ToUint64(), 0u);
  EXPECT_EQ(xlo->value.ToUint64(), 0x100000000u);
  EXPECT_EQ(zhi->value.ToUint64(), 0u);
  EXPECT_EQ(zlo->value.ToUint64(), 0u);
}

TEST(IntegerLiteralSim, WideDecimalLiteralTruncatesFromTheLeft) {
  SimFixture f;
  ASSERT_TRUE(RunSim(f,
                     "module t;\n"
                     "  logic [71:0] x;\n"
                     "  logic [7:0] hi;\n"
                     "  logic [63:0] lo;\n"
                     "  initial begin\n"
                     "    x = 72'd1208925819614629174706177;\n"
                     "    hi = x[71:64];\n"
                     "    lo = x[63:0];\n"
                     "  end\n"
                     "endmodule\n"));
  auto* hi = f.ctx.FindVariable("hi");
  auto* lo = f.ctx.FindVariable("lo");
  ASSERT_NE(hi, nullptr);
  ASSERT_NE(lo, nullptr);
  EXPECT_EQ(hi->value.ToUint64(), 0u);
  EXPECT_EQ(lo->value.ToUint64(), 1u);
}

TEST(IntegerLiteralSim, UnsizedBasedLiteralPastSixtyFourBitsKeepsItsDigits) {
  SimFixture f;
  ASSERT_TRUE(RunSim(f,
                     "module t;\n"
                     "  logic [95:0] y, b, o;\n"
                     "  logic [31:0] yhi, bhi, ohi;\n"
                     "  logic [63:0] olo;\n"
                     "  initial begin\n"
                     "    y = 'hF_FFFF_FFFF_FFFF_FFFF;\n"
                     "    b = 'b1000000000000000000000000000000000000"
                     "0000000000000000000000000000000000;\n"
                     "    o = 'o7777_7777_7777_7777_7777_7777;\n"
                     "    yhi = y[95:64];\n"
                     "    bhi = b[95:64];\n"
                     "    ohi = o[95:64];\n"
                     "    olo = o[63:0];\n"
                     "  end\n"
                     "endmodule\n"));
  auto* yhi = f.ctx.FindVariable("yhi");
  auto* bhi = f.ctx.FindVariable("bhi");
  auto* ohi = f.ctx.FindVariable("ohi");
  auto* olo = f.ctx.FindVariable("olo");
  ASSERT_NE(yhi, nullptr);
  ASSERT_NE(bhi, nullptr);
  ASSERT_NE(ohi, nullptr);
  ASSERT_NE(olo, nullptr);
  EXPECT_EQ(yhi->value.ToUint64(), 0xFu);
  EXPECT_EQ(bhi->value.ToUint64(), 0x40u);
  EXPECT_EQ(ohi->value.ToUint64(), 0xFFu);
  EXPECT_EQ(olo->value.ToUint64(), ~uint64_t{0});
}

TEST(IntegerLiteralSim, NewlineBetweenBaseAndDigitsKeepsTheValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'h\n"
      "    A5;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xA5u);
}

TEST(IntegerLiteralSim, NewlineBeforeTheDigitsLeavesTheUnsizedWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int n;\n"
      "  initial n = $bits('h\n"
      "    7_0000_0000);\n"
      "endmodule\n",
      f, "n");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 35u);
}

TEST(IntegerLiteralSim, WhiteSpaceBeforeTheDigitsOfAWideConstant) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  localparam logic [95:0] P = 96'h \n"
      "    3_0000_0000_0000_0000;\n"
      "  logic [31:0] hi;\n"
      "  initial hi = P[95:64];\n"
      "endmodule\n",
      f, "hi");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}
TEST(IntegerLiteralSim, UnsizedDecimalPastThirtyTwoBitsTakesItsMinimumWidth) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = $bits(4294967296);\n"
      "    b = $bits('d4294967296);\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 34u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 33u);
}

TEST(IntegerLiteralSim, SignedDecimalAtTwoToTheSixtyThreeStaysPositive) {
  SimFixture f;
  auto* hi = RunAndFindVar(
      "module t;\n"
      "  logic [127:0] y;\n"
      "  logic [63:0] hi;\n"
      "  int w;\n"
      "  initial begin\n"
      "    y = 9223372036854775808;\n"
      "    hi = y[127:64];\n"
      "    w = $bits(9223372036854775808);\n"
      "  end\n"
      "endmodule\n",
      f, "hi");
  ASSERT_NE(hi, nullptr);
  EXPECT_EQ(hi->value.ToUint64(), 0u);
  EXPECT_EQ(f.ctx.FindVariable("w")->value.ToUint64(), 65u);
}

TEST(IntegerLiteralSim, HighOrderXExtendsToTheWidthOfAnOperatorsOperands) {
  SimFixture f;
  auto* r = RunAndFindVar(
      "module t;\n"
      "  logic [63:0] a, b, c;\n"
      "  bit r, u, k;\n"
      "  initial begin\n"
      "    a = 'x;\n"
      "    r = (a === 'hx);\n"
      "    b = 64'd0 | 'hx;\n"
      "    u = &$isunknown(b[63:32]);\n"
      "    c = 64'd0 | 'h3x;\n"
      "    k = (c[63:32] === 32'd0);\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("u")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("k")->value.ToUint64(), 1u);
}

}  // namespace
