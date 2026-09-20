#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_param_value.h"

using namespace delta;

namespace {

// §20.6.2 (printed page 629): a typedef name that stands for a queue has no
// fixed size, so `$bits(qt)` written in a parameter's value is left to the
// run -- the typedef table the fold reads holds the element type alone, and
// the name is among those the elaborator records as standing for an unpacked
// aggregate -- rather than sized as one 8-bit element.
TEST(BitsOfDeclaration, QueueTypedefNameIsLeftToTheRun) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef byte qt[$];\n"
      "  localparam int BQ = $bits(qt);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ParamUnresolved(design, "BQ"));
}

// §11.4.3 (printed page 275): an addition carries out of bit 63 into the
// words above, so `P + 1` over a low word of all ones reads 2 above bit 64
// and 0 below, and a subtraction borrows from them, `P2 - 1` over a low word
// of zeros reading 1 above bit 64 and all ones below. 64b2dfbe0 folded both
// on the low word alone, which left `Q[95:64]` at P's own 1 and `B[63:32]` at
// 0.
TEST(WideOperators, AdditionCarriesAndSubtractionBorrowsAcrossBitSixtyFour) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [95:0] P = 96'h0000_0001_FFFF_FFFF_FFFF_FFFF;\n"
      "  localparam logic [95:0] P2 = 96'h0000_0002_0000_0000_0000_0000;\n"
      "  localparam logic [95:0] Q = P + 1;\n"
      "  localparam int QH = Q[95:64];\n"
      "  localparam int QL = Q[31:0];\n"
      "  localparam logic [95:0] B = P2 - 1;\n"
      "  localparam int BH = B[95:64];\n"
      "  localparam int BM = B[63:32];\n"
      "  localparam logic [95:0] D = P - 1;\n"
      "  localparam int DH = D[95:64];\n"
      "  localparam int DL = D[31:0];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "QH"), 2);
  EXPECT_EQ(ParamValue(design, "QL"), 0);
  EXPECT_EQ(ParamValue(design, "BH"), 1);
  EXPECT_EQ(ParamValue(design, "BM"), 0xFFFFFFFF);
  EXPECT_EQ(ParamValue(design, "DH"), 1);
  EXPECT_EQ(ParamValue(design, "DL"), 0xFFFFFFFE);
}

// §11.4.3.1 (printed page 277): where both operands are signed the narrower
// is sign-extended to the wider's size, so a 96-bit signed value plus the
// 8-bit signed -1 is that value less one -- 0 above bit 64 and all ones in
// the word below -- and not that value plus 255.
TEST(WideOperators, NarrowSignedOperandIsSignExtendedToTheWideOne) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic signed [95:0] PS = "
      "96'sh0000_0001_0000_0000_0000_0000;\n"
      "  localparam logic signed [95:0] SUM = PS + (-8'sd1);\n"
      "  localparam int SH = SUM[95:64];\n"
      "  localparam int SM = SUM[63:32];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "SH"), 0);
  EXPECT_EQ(ParamValue(design, "SM"), 0xFFFFFFFF);
}

// §11.4.5 (printed page 279): an equality compares every bit, so two values
// that differ above bit 64 alone are unequal; §11.4.4 (printed 278) orders
// unsigned values as unsigned, so the word above bit 64 decides `P < P2`
// where the low words agree and `P < P3` where the low word of P is the
// larger. 64b2dfbe0 compared the low words alone, which read P == P2 as 1
// and P < P3 as 0.
TEST(WideOperators, ComparisonReadsTheWordsAboveBitSixtyFour) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [95:0] P = 96'h0000_0001_FFFF_FFFF_FFFF_FFFF;\n"
      "  localparam logic [95:0] P2 = 96'h0000_0002_FFFF_FFFF_FFFF_FFFF;\n"
      "  localparam logic [95:0] P3 = 96'h0000_0002_0000_0000_0000_0000;\n"
      "  localparam bit E = (P == P2);\n"
      "  localparam bit ES = (P == P);\n"
      "  localparam bit NE = (P != P2);\n"
      "  localparam bit LT = (P < P2);\n"
      "  localparam bit LT3 = (P < P3);\n"
      "  localparam bit GT3 = (P > P3);\n"
      "  localparam bit LE3 = (P3 <= P);\n"
      "  localparam bit GE3 = (P3 >= P);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "E"), 0);
  EXPECT_EQ(ParamValue(design, "ES"), 1);
  EXPECT_EQ(ParamValue(design, "NE"), 1);
  EXPECT_EQ(ParamValue(design, "LT"), 1);
  EXPECT_EQ(ParamValue(design, "LT3"), 1);
  EXPECT_EQ(ParamValue(design, "GT3"), 0);
  EXPECT_EQ(ParamValue(design, "LE3"), 0);
  EXPECT_EQ(ParamValue(design, "GE3"), 1);
}

// §11.4.4 (printed page 278): where both operands are signed the comparison
// is between signed values, the sign being bit 95 of a 96-bit value, so a
// value with that bit set is below one with it clear however the words
// under it compare, and the same two values read unsigned order the other
// way.
TEST(WideOperators, SignedComparisonReadsTheSignAtTheTopWord) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic signed [95:0] NS = "
      "96'sh8000_0000_0000_0000_0000_0000;\n"
      "  localparam logic signed [95:0] PS = "
      "96'sh0000_0001_0000_0000_0000_0000;\n"
      "  localparam logic [95:0] NU = 96'h8000_0000_0000_0000_0000_0000;\n"
      "  localparam logic [95:0] PU = 96'h0000_0001_0000_0000_0000_0000;\n"
      "  localparam bit SLT = (NS < PS);\n"
      "  localparam bit ULT = (NU < PU);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "SLT"), 1);
  EXPECT_EQ(ParamValue(design, "ULT"), 0);
}

// §11.4.7 (printed page 280): a logical operator asks whether its operand is
// nonzero, which a value whose only set bit is above 64 is, so `HI && 1'b1`
// is 1 and `!HI` is 0; a low word of zeros alone would have said the
// opposite of both.
TEST(WideOperators, LogicalOperatorsReadEveryWordOfTheOperand) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [95:0] HI = 96'h0000_0001_0000_0000_0000_0000;\n"
      "  localparam bit AND = (HI && 1'b1);\n"
      "  localparam bit OR = (HI || 1'b0);\n"
      "  localparam bit NOT = !HI;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "AND"), 1);
  EXPECT_EQ(ParamValue(design, "OR"), 1);
  EXPECT_EQ(ParamValue(design, "NOT"), 0);
}

// §11.4.8 (printed page 281): the unary bitwise negation negates each bit of
// its operand, so `~P` above bit 64 is the complement of P's word there,
// and §11.4.3 (printed 277) makes unary minus the two's complement across
// every word, `-P` reading 0xFFFFFFFE above bit 64 and 1 in the low word.
// 64b2dfbe0 folded both on the low word and left the words above at 0.
TEST(WideOperators, NegationAndMinusWorkAcrossTheWideValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [95:0] P = 96'h0000_0001_FFFF_FFFF_FFFF_FFFF;\n"
      "  localparam logic [95:0] N = ~P;\n"
      "  localparam int NH = N[95:64];\n"
      "  localparam int NL = N[31:0];\n"
      "  localparam logic [95:0] NEG = -P;\n"
      "  localparam int NEGH = NEG[95:64];\n"
      "  localparam int NEGL = NEG[31:0];\n"
      "  localparam logic [95:0] POS = +P;\n"
      "  localparam int POSH = POS[95:64];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "NH"), 0xFFFFFFFE);
  EXPECT_EQ(ParamValue(design, "NL"), 0);
  EXPECT_EQ(ParamValue(design, "NEGH"), 0xFFFFFFFE);
  EXPECT_EQ(ParamValue(design, "NEGL"), 1);
  EXPECT_EQ(ParamValue(design, "POSH"), 1);
}

// §11.7 with §6.24.1 (printed page 139): a signing cast keeps every bit of
// its operand and sets the signedness alone, so `$unsigned(P)` and
// `$signed(P)` carry P's word above bit 64; a size cast pads or truncates to
// the size, so `128'(P)` keeps that word and pads with zeros above it,
// `128'(NS)` of a signed operand pads with its sign, and `32'(P)` keeps the
// low word alone. 64b2dfbe0 dropped the words above bit 64 through each.
TEST(WideOperators, CastsKeepTheWordsWithinTheWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [95:0] P = 96'h0000_0001_FFFF_FFFF_FFFF_FFFF;\n"
      "  localparam logic signed [95:0] NS = "
      "96'sh8000_0000_0000_0000_0000_0000;\n"
      "  localparam logic [95:0] U = $unsigned(P);\n"
      "  localparam int UH = U[95:64];\n"
      "  localparam logic signed [95:0] S = $signed(P);\n"
      "  localparam int SH = S[95:64];\n"
      "  localparam logic [127:0] W = 128'(P);\n"
      "  localparam int WH = W[127:96];\n"
      "  localparam int WM = W[95:64];\n"
      "  localparam logic [127:0] WS = 128'(NS);\n"
      "  localparam int WSH = WS[127:96];\n"
      "  localparam int WSM = WS[95:64];\n"
      "  localparam int LC = 32'(P);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "UH"), 1);
  EXPECT_EQ(ParamValue(design, "SH"), 1);
  EXPECT_EQ(ParamValue(design, "WH"), 0);
  EXPECT_EQ(ParamValue(design, "WM"), 1);
  EXPECT_EQ(ParamValue(design, "WSH"), 0xFFFFFFFF);
  EXPECT_EQ(ParamValue(design, "WSM"), 0x80000000);
  EXPECT_EQ(ParamValue(design, "LC"), 0xFFFFFFFF);
}

// §11.4.12 (printed pages 286-287): a concatenation joins its operands' bits
// with the first the most significant, each contributing its own width, so
// `{P, 4'h0}` is P shifted up by four and its bits 99:68 are P's 95:64;
// §11.4.12.1 (printed 287-288) makes `{2{P}}` two copies of P, whose bits
// 191:160 and 95:64 are both P's 95:64 and whose 127:96 are P's 31:0.
// 64b2dfbe0 read every non-literal operand as 32 bits and kept the low word
// alone.
TEST(WideOperators, ConcatenationAndReplicationCarryEveryWord) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [95:0] P = 96'h0000_0001_FFFF_FFFF_FFFF_FFFF;\n"
      "  localparam int CH = {P, 4'h0}[99:68];\n"
      "  localparam int CM = {P, 4'h0}[67:36];\n"
      "  localparam int CL = {P, 4'h0}[3:0];\n"
      "  localparam logic [99:0] C = {P, 4'h0};\n"
      "  localparam int CCH = C[99:68];\n"
      "  localparam int RH = {2{P}}[191:160];\n"
      "  localparam int RM = {2{P}}[127:96];\n"
      "  localparam int RL = {2{P}}[95:64];\n"
      "  localparam logic [191:0] R = {2{P}};\n"
      "  localparam int RRH = R[191:160];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "CH"), 1);
  EXPECT_EQ(ParamValue(design, "CM"), 0xFFFFFFFF);
  EXPECT_EQ(ParamValue(design, "CL"), 0);
  EXPECT_EQ(ParamValue(design, "CCH"), 1);
  EXPECT_EQ(ParamValue(design, "RH"), 1);
  EXPECT_EQ(ParamValue(design, "RM"), 0xFFFFFFFF);
  EXPECT_EQ(ParamValue(design, "RL"), 1);
  EXPECT_EQ(ParamValue(design, "RRH"), 1);
}

// §11.4.12 (printed page 286): an operand of a concatenation contributes its
// own width of bits, so `{A, A}` of a 4-bit parameter is the eight bits
// 0x55 and not the sixty-four that reading A as 32 bits made of it, and a
// signed operand contributes its bits without its sign fill, `{S4, 4'h0}`
// of a 4-bit signed -1 being 0xF0.
TEST(WideOperators, ConcatenationOperandContributesItsDeclaredWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam bit [3:0] A = 4'h5;\n"
      "  localparam int X = {A, A};\n"
      "  localparam bit signed [3:0] S4 = -1;\n"
      "  localparam int Y = {S4, 4'h0};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "X"), 0x55);
  EXPECT_EQ(ParamValue(design, "Y"), 0xF0);
}

// §11.4.3 (printed page 275): a product of operands wider than 64 bits is
// still folded on the low word -- the multi-word fold covers the additive,
// comparison, logical, unary, cast, concatenation and replication operators
// and not multiplication, division, modulus or power -- so `P * 2`, whose
// word above bit 64 is 3, reads 0 there and the doubled low word below. This
// pins the limit as d6a7eab50's TypedefNameIsLeftToTheRun pinned its own; a
// fold that carries the product across the words will invert it.
TEST(WideOperators, MultiplicationStaysOnTheLowWord) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [95:0] P = 96'h0000_0001_FFFF_FFFF_FFFF_FFFF;\n"
      "  localparam logic [95:0] MUL = P * 2;\n"
      "  localparam int MH = MUL[95:64];\n"
      "  localparam int ML = MUL[31:0];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "MH"), 0);
  EXPECT_EQ(ParamValue(design, "ML"), 0xFFFFFFFE);
}

// §6.20.2 (printed page 126): a parameter with a range specification has the
// range of its declaration, whichever way the bounds are written, so `logic
// [HI:1] V` under `localparam int HI = 8` is eight bits and `V[HI]` its top
// one (§11.5.1, printed 296). RtlirParamDecl::decl_width is folded without
// the earlier parameters in scope and is left at the vector's one bit where a
// bound names one, and 64b2dfbe0's RegisteredParamValue read that width, so
// V was cut to its low bit and `V[HI]` folded to 0; $bits(V) answered 1 from
// the same field. The bounds themselves fold against the parameters already
// elaborated, and the width is read from them now: 1 from `V[HI]`, 0 from
// `V[HI-1]` and 8 from $bits(V).
TEST(DeclaredWidth, RangeBoundWrittenAsAParameterSizesTheValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int HI = 8;\n"
      "  localparam logic [HI:1] V = 8'b1010_0101;\n"
      "  localparam W = V[HI];\n"
      "  localparam W6 = V[HI-1];\n"
      "  localparam int BV = $bits(V);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "W"), 1);
  EXPECT_EQ(ParamValue(design, "W6"), 0);
  EXPECT_EQ(ParamValue(design, "BV"), 8);
}

// The same declaration past 64 bits: `logic [TOP:0] P` under `localparam int
// TOP = 95` is 96 bits, and its words above bit 63 are read from the refold
// of its value only where the declared width is known to reach them. With
// the width read as one bit no refold was made, so `P[64]`, `P[TOP:64]` and
// $bits(P) folded to 0, 0 and 1 where 1, 1 and 96 are right; `P[65]` is 0
// either way and pins that the bit above the set one stays clear.
TEST(DeclaredWidth, RangeBoundWrittenAsAParameterReachesTheWordsAboveBit63) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int TOP = 95;\n"
      "  localparam logic [TOP:0] P = 96'h0000_0001_FFFF_FFFF_FFFF_FFFF;\n"
      "  localparam B64 = P[64];\n"
      "  localparam B65 = P[65];\n"
      "  localparam int PH = P[TOP:64];\n"
      "  localparam int BP = $bits(P);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "B64"), 1);
  EXPECT_EQ(ParamValue(design, "B65"), 0);
  EXPECT_EQ(ParamValue(design, "PH"), 1);
  EXPECT_EQ(ParamValue(design, "BP"), 96);
}

}  // namespace
