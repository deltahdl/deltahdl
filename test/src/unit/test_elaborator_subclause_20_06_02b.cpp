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

}  // namespace
