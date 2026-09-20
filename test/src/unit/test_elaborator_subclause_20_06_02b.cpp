#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_param_value.h"
#include "helpers_rtlir_lookup.h"

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

// §11.4.3 (printed page 275): a product carries across every word, so
// `P * 2`, P being 2^65 - 1, reads 3 above bit 64 and the doubled low word
// below; §11.6.1 (printed 299) sizes it by the wider operand, so `P * P`,
// which is 2^130 - 2^66 + 1, is cut to 96 bits and reads 0xFFFFFFFC above
// bit 64 and 1 in the low word. 994404a79 folded a product on the low word
// alone, which read 0 above bit 64 through both, and pinned that reading.
TEST(WideOperators, MultiplicationCarriesAcrossTheWords) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [95:0] P = 96'h0000_0001_FFFF_FFFF_FFFF_FFFF;\n"
      "  localparam logic [95:0] MUL = P * 2;\n"
      "  localparam int MH = MUL[95:64];\n"
      "  localparam int ML = MUL[31:0];\n"
      "  localparam logic [95:0] SQ = P * P;\n"
      "  localparam int SQH = SQ[95:64];\n"
      "  localparam int SQM = SQ[63:32];\n"
      "  localparam int SQL = SQ[31:0];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "MH"), 3);
  EXPECT_EQ(ParamValue(design, "ML"), 0xFFFFFFFE);
  EXPECT_EQ(ParamValue(design, "SQH"), 0xFFFFFFFC);
  EXPECT_EQ(ParamValue(design, "SQM"), 0);
  EXPECT_EQ(ParamValue(design, "SQL"), 1);
}

// §11.4.3 (printed page 275): the quotient truncates toward zero and the
// remainder is what the division leaves, so over Q = 4 * 2^64 + 7 the
// quotient by 3 is 2^64 + 0x5555_5555_5555_5557 -- 1 above bit 64,
// 0x55555555 in the word below and 0x55555557 at the bottom -- and the
// remainder is 2, since 2^64 leaves 1 by 3. A fold of the low word alone
// divides 7 by 3 and reads 0, 0, 2 and a remainder of 1.
TEST(WideOperators, DivisionAndRemainderReadEveryWord) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [95:0] Q = 96'h0000_0004_0000_0000_0000_0007;\n"
      "  localparam logic [95:0] D = Q / 3;\n"
      "  localparam int DH = D[95:64];\n"
      "  localparam int DM = D[63:32];\n"
      "  localparam int DL = D[31:0];\n"
      "  localparam logic [95:0] R = Q % 3;\n"
      "  localparam int RH = R[95:64];\n"
      "  localparam int RL = R[31:0];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "DH"), 1);
  EXPECT_EQ(ParamValue(design, "DM"), 0x55555555);
  EXPECT_EQ(ParamValue(design, "DL"), 0x55555557);
  EXPECT_EQ(ParamValue(design, "RH"), 0);
  EXPECT_EQ(ParamValue(design, "RL"), 2);
}

// §11.4.3 (printed page 275) with §11.4.3.1 (printed 277): two signed
// operands divide as signed values, the quotient truncating toward zero and
// the remainder taking the sign of the first operand. NQ is -(4 * 2^64 + 5),
// so `NQ / 3` is -(2^64 + 0x5555_5555_5555_5557), whose 96 bits read
// 0xFFFFFFFE above bit 64 and 0xAAAAAAA9 at the bottom, and `NQ % 3` is 0,
// 4 * 2^64 + 5 being 6 by 3 and so a multiple of it. A fold of the low word
// alone divides -5 by 3 and reads 0 in the quotient's word above 64 and a
// remainder of -2.
TEST(WideOperators, SignedDivisionTakesTheSignsAcrossTheWords) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic signed [95:0] NQ = "
      "-96'sh0000_0004_0000_0000_0000_0005;\n"
      "  localparam logic signed [95:0] SQ = NQ / 96'sd3;\n"
      "  localparam int SQH = SQ[95:64];\n"
      "  localparam int SQM = SQ[63:32];\n"
      "  localparam int SQL = SQ[31:0];\n"
      "  localparam logic signed [95:0] SR = NQ % 96'sd3;\n"
      "  localparam int SRH = SR[95:64];\n"
      "  localparam int SRL = SR[31:0];\n"
      "  localparam logic signed [95:0] PR = 96'sd11 % (-96'sd3);\n"
      "  localparam int PRL = PR[31:0];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "SQH"), 0xFFFFFFFE);
  EXPECT_EQ(ParamValue(design, "SQM"), 0xAAAAAAAA);
  EXPECT_EQ(ParamValue(design, "SQL"), 0xAAAAAAA9);
  EXPECT_EQ(ParamValue(design, "SRH"), 0);
  EXPECT_EQ(ParamValue(design, "SRL"), 0);
  EXPECT_EQ(ParamValue(design, "PRL"), 2);
}

// §11.4.3's Table 11-4 (printed page 276): a positive exponent raises the
// base that many times, cut to the width, so `96'd3 ** 50` reads 0x9805
// above bit 64, 0x53F0DB2F in the word below and 0xD09DE3C9 at the bottom,
// `96'd2 ** 95` sets bit 95 alone and `96'd2 ** 96` leaves nothing; a zero
// exponent answers 1 whatever the base, and a negative one 1 for a base of
// 1, -1 or 1 by its parity for a base of -1 and 0 for a larger base. A fold
// of the low word alone reads 0 above bit 64 through the first two.
TEST(WideOperators, PowerFollowsTableElevenFourAcrossTheWords) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [95:0] PW = 96'd3 ** 50;\n"
      "  localparam int PWH = PW[95:64];\n"
      "  localparam int PWM = PW[63:32];\n"
      "  localparam int PWL = PW[31:0];\n"
      "  localparam logic [95:0] TOP = 96'd2 ** 95;\n"
      "  localparam int TOPH = TOP[95:64];\n"
      "  localparam int TOPL = TOP[31:0];\n"
      "  localparam logic [95:0] OVER = 96'd2 ** 96;\n"
      "  localparam int OVERH = OVER[95:64];\n"
      "  localparam logic [95:0] ZERO = 96'd7 ** 0;\n"
      "  localparam int ZEROL = ZERO[31:0];\n"
      "  localparam logic signed [95:0] ONE = 96'sd1 ** (-96'sd3);\n"
      "  localparam int ONEL = ONE[31:0];\n"
      "  localparam logic signed [95:0] ODD = (-96'sd1) ** (-96'sd3);\n"
      "  localparam int ODDH = ODD[95:64];\n"
      "  localparam logic signed [95:0] EVEN = (-96'sd1) ** (-96'sd2);\n"
      "  localparam int EVENL = EVEN[31:0];\n"
      "  localparam logic signed [95:0] BIG = 96'sd5 ** (-96'sd1);\n"
      "  localparam int BIGL = BIG[31:0];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "PWH"), 0x9805);
  EXPECT_EQ(ParamValue(design, "PWM"), 0x53F0DB2F);
  EXPECT_EQ(ParamValue(design, "PWL"), 0xD09DE3C9);
  EXPECT_EQ(ParamValue(design, "TOPH"), 0x80000000);
  EXPECT_EQ(ParamValue(design, "TOPL"), 0);
  EXPECT_EQ(ParamValue(design, "OVERH"), 0);
  EXPECT_EQ(ParamValue(design, "ZEROL"), 1);
  EXPECT_EQ(ParamValue(design, "ONEL"), 1);
  EXPECT_EQ(ParamValue(design, "ODDH"), 0xFFFFFFFF);
  EXPECT_EQ(ParamValue(design, "EVENL"), 1);
  EXPECT_EQ(ParamValue(design, "BIGL"), 0);
}

// §11.4.3 (printed page 275): a division or a remainder by zero is x, which
// no parameter value folds to, so each is left unresolved as the 64-bit fold
// leaves them.
TEST(WideOperators, DivisionByZeroFoldsToNothing) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [95:0] P = 96'h0000_0001_FFFF_FFFF_FFFF_FFFF;\n"
      "  localparam logic [95:0] DZ = P / 96'd0;\n"
      "  localparam logic [95:0] RZ = P % 96'd0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ParamUnresolved(design, "DZ"));
  EXPECT_TRUE(ParamUnresolved(design, "RZ"));
}

// The resolved value of parameter `name` of module `mod`, or -1 where the
// design holds no such module or parameter or the fold left it unresolved,
// for a reading of a parameter of an instantiated module.
int64_t ParamValueIn(RtlirDesign* design, std::string_view mod,
                     std::string_view name) {
  const auto* p = FindParam(design, mod, name);
  return p != nullptr && p->is_resolved ? p->resolved_value : -1;
}

// §23.10.2 (printed page 766) with §6.20.2 (printed 126): an instance's
// parameter value assignment by name gives the parameter the value of an
// expression written in the instantiating module, and the parameter keeps
// its declared range, so `c #(.P(PP)) u()` under a 96-bit PP gives c's P
// every bit of PP and `P[95:64]` in c reads PP's word above 64. 64b2dfbe0
// refolded a literal override alone for the words above bit 63, so an
// override written as the parent's parameter read 0 there.
TEST(ParamOverride, NamedOverrideWrittenAsAParameterReadsAboveBitSixtyFour) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module c #(parameter logic [95:0] P = 96'h1);\n"
      "  localparam int H = P[95:64];\n"
      "  localparam int L = P[31:0];\n"
      "endmodule\n"
      "module t;\n"
      "  localparam logic [95:0] PP = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "  c #(.P(PP)) u();\n"
      "endmodule\n",
      f, "t");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValueIn(design, "c", "H"), 0x01234567);
  EXPECT_EQ(ParamValueIn(design, "c", "L"), 0x00112233);
}

// §23.10.2.1 (printed page 766): an assignment by ordered list gives the
// parameters their values in the order of their declaration, so `c #(PP)
// u()` is the same override as `.P(PP)` and reads the same word above 64,
// and an expression over the parent's parameter, `PP + 1`, is folded there
// and carried across every word.
TEST(ParamOverride, OrderedOverrideWrittenAsAParameterReadsAboveBitSixtyFour) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module c #(parameter logic [95:0] P = 96'h1, parameter logic [95:0] "
      "Q = 96'h1);\n"
      "  localparam int H = P[95:64];\n"
      "  localparam int QH = Q[95:64];\n"
      "  localparam int QL = Q[31:0];\n"
      "endmodule\n"
      "module t;\n"
      "  localparam logic [95:0] PP = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "  localparam logic [95:0] PF = 96'h0000_0001_FFFF_FFFF_FFFF_FFFF;\n"
      "  c #(PP, PF + 1) u();\n"
      "endmodule\n",
      f, "t");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValueIn(design, "c", "H"), 0x01234567);
  EXPECT_EQ(ParamValueIn(design, "c", "QH"), 2);
  EXPECT_EQ(ParamValueIn(design, "c", "QL"), 0);
}

// §23.10.1 (printed pages 764-765): a defparam gives the parameter it names
// the value of an expression written in the module holding the statement,
// and a parameter whose value depends on it takes its new value too
// (§23.10.2, printed 766). Over a 96-bit P of c, `defparam u.P = PP` under
// the parent's 96-bit PP and `defparam v.P = 96'h...` a literal each give P
// their words above 64, and `P[95:64]` in c, made over after the defparam,
// reads them. 64b2dfbe0 refolded the literal alone, and made c's dependent
// parameters over with the parent registered, under which c's P was read at
// 32 bits, so H read 0 through both.
TEST(ParamOverride, DefparamValueReadsAboveBitSixtyFour) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module c #(parameter logic [95:0] P = 96'h1);\n"
      "  localparam int H = P[95:64];\n"
      "  localparam int L = P[31:0];\n"
      "endmodule\n"
      "module d #(parameter logic [95:0] P = 96'h1);\n"
      "  localparam int H = P[95:64];\n"
      "endmodule\n"
      "module t;\n"
      "  localparam logic [95:0] PP = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "  c u();\n"
      "  d v();\n"
      "  defparam u.P = PP;\n"
      "  defparam v.P = 96'h0000_0002_FFFF_FFFF_FFFF_FFFF;\n"
      "endmodule\n",
      f, "t");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValueIn(design, "c", "H"), 0x01234567);
  EXPECT_EQ(ParamValueIn(design, "c", "L"), 0x00112233);
  EXPECT_EQ(ParamValueIn(design, "d", "H"), 2);
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

// §11.4.3's Table 11-4 (printed page 276): a zero base raised to a negative
// power is x, which no parameter value folds to, so `localparam int Z = 0 **
// -1` is left unresolved as a division by zero is, among a module's items
// and in a parameter port list alike. §6.20.2 (printed 127) applies the
// real-to-integer conversion to a parameter whose value is real, and both
// fold sites refolded an integral expression the integer fold had declined
// as a real instead, through std::pow(0, -1), inf, and std::llround of it,
// which is undefined, so Z read as resolved to whatever that made. A real
// zero base to a negative power, unspecified by §11.4.3, is left unresolved
// as well.
TEST(RealFold, ZeroToANegativePowerStaysUnresolved) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter int ZP = 0 ** -1);\n"
      "  localparam int Z = 0 ** -1;\n"
      "  localparam int ZR = 0.0 ** -1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ParamUnresolved(design, "ZP"));
  EXPECT_TRUE(ParamUnresolved(design, "Z"));
  EXPECT_TRUE(ParamUnresolved(design, "ZR"));
}

// §6.20.2 (printed page 127) with §6.12.1: a value with a real operand still
// takes the real path, so `localparam real R = 2.0 ** -1` is 0.5, `localparam
// int I = 2.0 ** 2` rounds to 4 among the items and `IP = 2.5 * 2` to 5 in
// the port list, and `localparam int T = 3000ps`, a time literal §5.8 makes a
// real in the ns unit, is 3.
TEST(RealFold, RealOperandStillRoundsToTheNearestInteger) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m #(parameter int IP = 2.5 * 2);\n"
      "  localparam real R = 2.0 ** -1;\n"
      "  localparam int I = 2.0 ** 2;\n"
      "  localparam int T = 3000ps;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "IP"), 5);
  EXPECT_EQ(ParamValue(design, "I"), 4);
  EXPECT_EQ(ParamValue(design, "T"), 3);
  const auto* r = FindParam(design, "m", "R");
  ASSERT_NE(r, nullptr);
  EXPECT_TRUE(r->is_real_value);
  EXPECT_DOUBLE_EQ(r->resolved_real, 0.5);
}

// §6.20.2 (printed pages 126-127): a parameter declared with neither type nor
// range takes the type and range of the final value assigned to it, after
// the overrides, a logic vector as wide as that value, so `parameter P = 1`
// overridden with the parent's 96-bit PP (§23.10.2, printed 766) is 96 bits
// in c: `$bits(P)` reads 96 and `P[95:64]` PP's word above 64. 082e4d682
// recorded the words above bit 63 for a declaration that fixes a width
// alone, and sized an override only where it was a literal, so P read at 32
// bits, H as 0 and $bits(P) as nothing.
TEST(ParamOverride, UntypedParameterTakesTheWidthOfAParameterOverride) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module c #(parameter P = 1);\n"
      "  localparam int B = $bits(P);\n"
      "  localparam int H = P[95:64];\n"
      "  localparam int L = P[31:0];\n"
      "endmodule\n"
      "module t;\n"
      "  localparam logic [95:0] PP = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "  c #(.P(PP)) u();\n"
      "endmodule\n",
      f, "t");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValueIn(design, "c", "B"), 96);
  EXPECT_EQ(ParamValueIn(design, "c", "L"), 0x00112233);
  EXPECT_EQ(ParamValueIn(design, "c", "H"), 0x01234567);
}

// The same parameter under a literal override of 96 bits, and one of 8: each
// gives P the literal's own width, 96 with the word above 64 read through
// `P[95:64]`, and 8 through `$bits(P)`; the default `parameter P = 1` with
// no override keeps the 32 bits of its unsized value.
TEST(ParamOverride, UntypedParameterTakesTheWidthOfALiteralOverride) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module c #(parameter P = 1);\n"
      "  localparam int H = P[95:64];\n"
      "  localparam int B = $bits(P);\n"
      "endmodule\n"
      "module d #(parameter P = 1);\n"
      "  localparam int B = $bits(P);\n"
      "  localparam int V = P;\n"
      "endmodule\n"
      "module e #(parameter P = 1);\n"
      "  localparam int B = $bits(P);\n"
      "endmodule\n"
      "module t;\n"
      "  c #(.P(96'h0000_0002_FFFF_FFFF_0000_0001)) u();\n"
      "  d #(.P(8'd5)) v();\n"
      "  e w();\n"
      "endmodule\n",
      f, "t");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValueIn(design, "c", "H"), 2);
  EXPECT_EQ(ParamValueIn(design, "c", "B"), 96);
  EXPECT_EQ(ParamValueIn(design, "d", "B"), 8);
  EXPECT_EQ(ParamValueIn(design, "d", "V"), 5);
  EXPECT_EQ(ParamValueIn(design, "e", "B"), 32);
}

// §23.10.1 (printed page 765): a defparam's value, written in the module
// holding the statement, is the final value of an untyped parameter too, so
// `defparam u.P = PP` under the parent's 96-bit PP makes c's P 96 bits, and
// H, made over after the defparam, reads PP's word above 64.
TEST(ParamOverride, UntypedParameterTakesTheWidthOfADefparamValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module c #(parameter P = 1);\n"
      "  localparam int H = P[95:64];\n"
      "  localparam int B = $bits(P);\n"
      "endmodule\n"
      "module t;\n"
      "  localparam logic [95:0] PP = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "  c u();\n"
      "  defparam u.P = PP;\n"
      "endmodule\n",
      f, "t");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValueIn(design, "c", "H"), 0x01234567);
  EXPECT_EQ(ParamValueIn(design, "c", "B"), 96);
}

}  // namespace
