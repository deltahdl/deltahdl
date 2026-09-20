#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_scheduler.h"

namespace {

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

TEST(IntegerLiteralSim, LiteralInTernaryCondition) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 1 ? 8'd99 : 8'd0;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(v, 99u);
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

// §5.7.1 final paragraph, met at the declaration initializer rather than at a
// procedural assignment: `int c = 4'shf` is the assignment `c = 4'shf` made
// before any procedure runs (§6.8), and the sized signed literal is
// sign-extended into the 32-bit int, so c is -1. The initializer lowering
// widened the 4-bit value through its unsigned integer and read 15, where the
// procedural `initial c = 4'shf` beside it read -1.
TEST(IntegerLiteralSim, SignedLiteralInitializerSignExtendsIntoInt) {
  auto result = RunAndGet(
      "module t;\n"
      "  int c = 4'shf;\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(result & 0xFFFFFFFFu, 0xFFFFFFFFu);
}

// §5.7.1 final paragraph with §6.11.1: integer is a 32-bit signed 4-state
// object, and the initializer's sized signed literal is sign-extended into it
// as into an int.
TEST(IntegerLiteralSim, SignedLiteralInitializerSignExtendsIntoInteger) {
  auto result = RunAndGet(
      "module t;\n"
      "  integer g = 4'shf;\n"
      "endmodule\n",
      "g");
  EXPECT_EQ(result & 0xFFFFFFFFu, 0xFFFFFFFFu);
}

// §5.7.1 final paragraph: the object is an unsigned logic vector, and the
// literal is still sign-extended, the clause saying the object's own
// signedness does not decide. 4'shf into 16 bits is ffff, not 000f.
TEST(IntegerLiteralSim, SignedLiteralInitializerSignExtendsIntoWiderLogic) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [15:0] b = 4'shf;\n"
      "endmodule\n",
      "b");
  EXPECT_EQ(result & 0xFFFFu, 0xFFFFu);
}

// §5.7.1 final paragraph: an 8-bit signed literal whose high bit is set,
// 8'sh85, is -123 and fills the 16-bit object as ff85. The low byte
// discriminates a sign fill from a value the widening misread.
TEST(IntegerLiteralSim, SignedHexLiteralInitializerSignExtendsHighByte) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [15:0] d = 8'sh85;\n"
      "endmodule\n",
      "d");
  EXPECT_EQ(result & 0xFFFFu, 0xFF85u);
}

// §5.7.1 final paragraph: a sized negative signed literal, -8'sd6, is the
// 8-bit signed value fa and is sign-extended into the int, reading -6 rather
// than 250.
TEST(IntegerLiteralSim, NegativeSignedLiteralInitializerSignExtendsIntoInt) {
  auto result = RunAndGet(
      "module t;\n"
      "  int f = -8'sd6;\n"
      "endmodule\n",
      "f");
  EXPECT_EQ(result & 0xFFFFFFFFu, 0xFFFFFFFAu);
}

// Discriminates the four above: the same 8'h85 without the s designator is an
// unsigned literal, so the initializer zero-extends it to 0085. Only the
// literal's signedness decides the fill, in an initializer as in a procedural
// assignment.
TEST(IntegerLiteralSim, UnsignedLiteralInitializerZeroExtendsIntoWiderLogic) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [15:0] e = 8'h85;\n"
      "endmodule\n",
      "e");
  EXPECT_EQ(result & 0xFFFFu, 0x0085u);
}

// §5.7.1's final paragraph with §11.6.1 and §11.8.2: the operand of a unary
// minus is context-determined (Table 11-21 keeps only `!` and the reductions
// self-determined), so in `logic [15:0] a = -8'd6` the 8-bit literal is
// extended to the 16 bits of the assignment before it is negated, and the
// object holds the 16-bit two's complement fffa. The negation was done at the
// literal's 8 bits and the 8-bit fa then zero-extended to 00fa.
TEST(IntegerLiteralSim,
     NegativeUnsignedLiteralInitializerNegatesAtTargetWidth) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [15:0] a = -8'd6;\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(result & 0xFFFFu, 0xFFFAu);
}

// §11.6.1 with §6.20.2: a parameter's value expression is the right-hand side
// of an assignment to the parameter, so its declared 16 bits size the operand
// of the negation as a variable's do.
TEST(IntegerLiteralSim,
     NegativeUnsignedLiteralParameterNegatesAtDeclaredWidth) {
  auto result = RunAndGet(
      "module t;\n"
      "  parameter logic [15:0] V = -8'd6;\n"
      "  logic [15:0] a = V;\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(result & 0xFFFFu, 0xFFFAu);
}

// §8.7 with §6.8: a class property's initializer is an assignment to the
// property, so the 16 bits the property declares size the negation's operand
// as a module variable's do; the property's initializer was evaluated
// self-determined and its 8-bit fa widened afterwards, reading 00fa.
TEST(IntegerLiteralSim, NegativeUnsignedLiteralClassPropertyNegatesAtWidth) {
  auto result = RunAndGet(
      "module t;\n"
      "  class C;\n"
      "    logic [15:0] v = -8'd6;\n"
      "  endclass\n"
      "  logic [15:0] a;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = new;\n"
      "    a = c.v;\n"
      "  end\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(result & 0xFFFFu, 0xFFFAu);
}

// Discriminates the three above from a sign extension of the literal: `8'd6`
// is unsigned, so extending it first gives 16'd6 and the negation fffa, while
// a negation at 8 bits followed by a sign extension of the unsigned fa would
// also give fffa. `-8'd130` tells them apart: extended first it is
// -130 = ff7e; negated at 8 bits it is 7e, whose high bit is clear, and no
// extension of that reads ff7e.
TEST(IntegerLiteralSim, NegativeUnsignedLiteralAboveHalfRangeNegatesAtWidth) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [15:0] a = -8'd130;\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(result & 0xFFFFu, 0xFF7Eu);
}

// §11.6.1 Table 11-21 gives `~` the same L(i) row as unary minus, so its
// operand is extended to the context before the inversion: `~8'hFF` into 16
// bits inverts sixteen bits of 00ff to ff00, not eight bits to 00 and then
// widens.
TEST(IntegerLiteralSim, BitwiseNotOfSizedLiteralInvertsAtTargetWidth) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [15:0] a = ~8'hFF;\n"
      "endmodule\n",
      "a");
  EXPECT_EQ(result & 0xFFFFu, 0xFF00u);
}

}  // namespace
