#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_param_value.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'$bits' cannot be applied directly to dynamically sized type 'qt'", 3,
      "20.6.2"));
}

TEST(BitsOfDeclaration, BitsOfADynamicallySizedVariableIsNoConstant) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] q[$];\n"
      "  logic [7:0] d[];\n"
      "  logic [7:0] a[int];\n"
      "  string t;\n"
      "  logic [7:0] s[4];\n"
      "  localparam int BQ = $bits(q);\n"
      "  localparam int BD = $bits(d);\n"
      "  localparam int BA = $bits(a);\n"
      "  localparam int BT = $bits(t);\n"
      "  localparam int BS = $bits(s);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "localparam 'BQ' initializer is not a constant "
                            "expression",
                            7, "6.20.4"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "localparam 'BD' initializer is not a constant "
                            "expression",
                            8, "6.20.4"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "localparam 'BA' initializer is not a constant "
                            "expression",
                            9, "6.20.4"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "localparam 'BT' initializer is not a constant "
                            "expression",
                            10, "6.20.4"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "localparam 'BS' initializer is not a constant "
                             "expression",
                             11, "6.20.4"));
}

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

TEST(WideOperators, ContextDeterminedBaseIsRaisedAtTheTargetsWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [95:0] X = 3 ** 50;\n"
      "  localparam int XH = X[95:64];\n"
      "  localparam int XM = X[63:32];\n"
      "  localparam int XL = X[31:0];\n"
      "  localparam logic [63:0] Z = 32'hFFFF_FFFF + 1;\n"
      "  localparam int ZH = Z[63:32];\n"
      "  localparam int ZL = Z[31:0];\n"
      "  localparam int BX = $bits(3 ** 50);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "XH"), 0x9805);
  EXPECT_EQ(ParamValue(design, "XM"), 0x53F0DB2F);
  EXPECT_EQ(ParamValue(design, "XL"), 0xD09DE3C9);
  EXPECT_EQ(ParamValue(design, "ZH"), 1);
  EXPECT_EQ(ParamValue(design, "ZL"), 0);
  EXPECT_EQ(ParamValue(design, "BX"), 32);
}

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

int64_t ParamValueIn(RtlirDesign* design, std::string_view mod,
                     std::string_view name) {
  const auto* p = FindParam(design, mod, name);
  return p != nullptr && p->is_resolved ? p->resolved_value : -1;
}

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

TEST(ParamOverride, OverrideExpressionIsSizedByTheParametersDeclaredWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module c #(parameter [15:0] P = 0, parameter logic [95:0] W = 0);\n"
      "  localparam int PV = P;\n"
      "  localparam int WH = W[95:64];\n"
      "endmodule\n"
      "module d;\n"
      "  parameter [15:0] P = 0;\n"
      "  localparam int PV = P;\n"
      "endmodule\n"
      "module t;\n"
      "  c #(.P(8'hAB << 8), .W(3 ** 50)) u();\n"
      "  d #(.P(8'hAB << 8)) v();\n"
      "endmodule\n",
      f, "t");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValueIn(design, "c", "PV"), 0xAB00);
  EXPECT_EQ(ParamValueIn(design, "c", "WH"), 0x9805);
  EXPECT_EQ(ParamValueIn(design, "d", "PV"), 0xAB00);
}

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
