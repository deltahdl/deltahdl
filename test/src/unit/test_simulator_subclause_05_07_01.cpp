

#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
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

TEST(IntegerLiteralSim, SimpleDecimalNumber) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = 659;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 659u);
}

TEST(IntegerLiteralSim, SizedBinaryLiteral) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 4'b1001;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 9u);
}

TEST(IntegerLiteralSim, SizedOctalLiteral) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial x = 12'o7460;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 07460u);
}

TEST(IntegerLiteralSim, SizedDecimalLiteral) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 5'd3;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 3u);
}

TEST(IntegerLiteralSim, UnsizedHexLiteral) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = 'h837FF;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 0x837FFu);
}

TEST(IntegerLiteralSim, UnsizedOctalLiteral) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = 'o7460;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 07460u);
}

TEST(IntegerLiteralSim, TruncationFromLeft) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 4'b11001;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 0x09u);
}

TEST(IntegerLiteralSim, SignedBasedLiteral) {
  auto result = RunAndGet(
      "module t;\n"
      "  integer x;\n"
      "  initial x = 4'shf;\n"
      "endmodule\n",
      "x");
  uint32_t mask = 0xFFFFFFFF;
  EXPECT_EQ(result & mask, mask);
}

TEST(IntegerLiteralSim, SizeConstantNonzero) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 1'b1;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 1u);
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

TEST(IntegerLiteralSim, LiteralInTernaryCondition) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 1 ? 8'd99 : 8'd0;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(v, 99u);
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

TEST(IntegerLiteralSim, LeftPadZWhenLeftmostIsZ) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'hz5;\n"
      "endmodule\n",
      "x");

  EXPECT_EQ(result & 0x0Fu, 0x05u);
}

TEST(IntegerLiteralSim, UnsizedDefaultWidth32Bits) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = 'hFFFF_FFFF;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 0xFFFFFFFFu);
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

TEST(IntegerLiteralSim, SizedHexLiteralValue) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = 20'h837FF;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 0x837FFu);
}

TEST(IntegerLiteralSim, UnsizedValueAboveU32WidensBeyond32Bits) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [63:0] x;\n"
      "  initial x = 'h1_0000_0000;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 0x100000000ull);
}

TEST(IntegerLiteralSim, SimpleDecimalNegativeSignExtends) {
  auto result = RunAndGet(
      "module t;\n"
      "  integer x;\n"
      "  initial x = -1;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result & 0xFFFFFFFFu, 0xFFFFFFFFu);
}

TEST(IntegerLiteralSim, BaseOnlyDoesNotSignExtend) {
  auto result = RunAndGet(
      "module t;\n"
      "  integer x;\n"
      "  initial x = 4'hf;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result & 0xFFFFFFFFu, 0x0000000Fu);
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
  // Both words of the 64-bit vector must report all-x.
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
  // All 64 bits must report high-impedance: aval=0, bval=1 per bit.
  EXPECT_EQ(var->value.words[0].aval, uint64_t{0});
  EXPECT_EQ(var->value.words[0].bval, ~uint64_t{0});
}

TEST(IntegerLiteralSim, NegativeSizedLiteralIsTwosComplement) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = -8'sd6;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result & 0xFFu, 0xFAu);
}

TEST(IntegerLiteralSim, SignedLiteralSignExtendsIntoUnsignedLogic) {
  // §5.7.1 final paragraph: a sized signed literal is sign-extended when
  // assigned to a logic object regardless of whether that object's type is
  // signed. The 4-bit signed literal 4'shf is -1; widened into the unsigned
  // 8-bit logic target it must become 0xFF (sign fill), not 0x0F (zero fill).
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 4'shf;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result & 0xFFu, 0xFFu);
}

TEST(IntegerLiteralSim, UnsignedLiteralZeroExtendsIntoUnsignedLogic) {
  // Discriminates the rule above: the same value with no s designator is an
  // unsigned literal, so widening into the identical unsigned 8-bit logic
  // target zero-fills to 0x0F. Only the literal's signedness — not the
  // target's — decides between sign fill and zero fill.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 4'hf;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result & 0xFFu, 0x0Fu);
}

TEST(IntegerLiteralSim, UnbasedUnsizedIsOneBitInConcatenation) {
  // {1'b1, '1, 1'b0} must be a 3-bit value (0b110 == 6) — the
  // unbased unsized literal contributes a single bit in the
  // self-determined concatenation operand position. If '1 carried
  // its default wide width instead, the concatenation would be
  // tens of bits and the lower bits would still match the 32-bit
  // target — so the test pins a wider target and a value that only
  // matches when the operand really is one bit.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = {1'b1, '1, 1'b0};\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 0x6u);
}

TEST(IntegerLiteralSim, UnbasedUnsizedIsOneBitInReplication) {
  // {4{'1}} replicates a single bit four times, producing a 4-bit
  // value of all ones (0xF). The target here is 32 bits, so without
  // the self-determined rule '1 would carry its default width and
  // the replicated result would span tens of bits whose lower
  // portion would still saturate the target.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = {4{'1}};\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 0xFu);
}

// §5.7.1: a sized negative literal is sign-extended when assigned to a logic
// object. -4'sd1 is a 4-bit signed -1; widened into the 8-bit target it fills
// with the sign bit to 0xFF, not 0x0F. Distinct input form from the s-only
// literal (this one forms the negative via a leading unary minus).
TEST(IntegerLiteralSim, NegativeLiteralSignExtendsIntoWiderLogic) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = -4'sd1;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result & 0xFFu, 0xFFu);
}

// §5.7.1: an unsized signed number must reserve a sign bit, so a value between
// 2^31 and 2^32 stays non-negative rather than collapsing to a 32-bit negative.
// The plain decimal 2147483648 is signed and unsized; widened into the 64-bit
// signed target it must remain +2147483648, which only holds if the literal
// reserved a 33rd (sign) bit instead of stopping at 32.
TEST(IntegerLiteralSim, UnsizedSignedValueReservesSignBit) {
  auto result = RunAndGet(
      "module t;\n"
      "  longint x;\n"
      "  initial x = 2147483648;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 2147483648ull);
}

// §5.7.1: the '?' digit is the z alternative and, in a hexadecimal literal,
// sets four bits to high-impedance. Here the low hex digit '?' drives bits 0-3
// to z (aval=0, bval=1) while the known high digit 5 stays a plain value.
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

// §5.7.1: in an octal literal the '?' digit sets three bits to high-impedance.
// The low octal digit '?' drives bits 0-2 to z while the high digit 7 stays a
// known value.
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

// §5.7.1 (final paragraph): an integer literal constant is a logic vector with
// range [n-1:0]. Built end-to-end on the §7.4 packed-vector dependency: the
// literal is stored in a real logic [7:0] packed vector and part-selected, so
// the high nibble reads 0xA and the low nibble 0x5 — observing the literal laid
// out MSB-first across the vector's bit range rather than as an opaque scalar.
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

// §5.7.1: the digits of a decimal literal form its value at the width its size
// constant states, so `81'd1208925819614629174706177` (2^80 + 1) sets bit 80
// as well as bit 0. Expr::int_val carries the value's low 64 bits alone, and a
// run-time value built from it read the high seventeen bits as 0.
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

// §5.7.1: an unsized number that needs more than 32 bits has at least the
// width that represents its value, a sign bit included for a signed one, so
// the simple decimal 1180591620717411303424 (2^70) is at least 72 bits and
// keeps bit 70 into a 96-bit target. Sized from Expr::int_val, whose 64 bits
// hold 2^70 as 0, the literal was 32 bits of zero.
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

// §5.7.1: a decimal literal wider than 64 bits whose value is 0 or fits in one
// word is padded to the left with zeros, `_` separators dropped -- the same
// digit fold as the wide value above, on values the 64-bit path already got
// right.
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

// §5.7.1: an unsigned number larger than the size constant is truncated from
// the left, so 2^80 + 1 written under a size of 72 keeps bits 0 to 71 alone
// and reads 1.
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

// §5.7.1: an unsized based number has at least the width its value needs, so
// the 17-digit `'hF_FFFF_FFFF_FFFF_FFFF` is 68 bits, `'b1` over 70 zeros 71
// and the 24-digit octal all-sevens 72, each carrying its top digit into a
// 96-bit target. Sized from Expr::int_val, whose 64 bits are the value's low
// word, each was 64 bits and read 0 above bit 63.
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

// §5.7.1's own example: the unsized `'h7_0000_0000` is at least 35 bits, the
// three the leading 7 needs over eight zero digits; the 17-digit all-ones hex
// literal above is 68. A based value past 32 bits was sized 64 outright.
TEST(IntegerLiteralSim, UnsizedHexLiteralIsAsWideAsItsDigitsNeed) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [63:0] n;\n"
      "  initial n = {$bits('hF_FFFF_FFFF_FFFF_FFFF), $bits('h7_0000_0000)};\n"
      "endmodule\n",
      "n");
  EXPECT_EQ(result, 0x0000004400000023u);
}

}  // namespace
