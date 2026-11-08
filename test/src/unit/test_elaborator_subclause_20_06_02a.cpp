#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "fixture_evaluator.h"
#include "helpers_param_value.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

TEST(ConstEval, BitsExpr) {
  EvalFixture f;

  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$bits(8'hFF)", f)), 8);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$bits(16'h0)", f)), 16);
}

TEST(ConstEval, BitsOfBuiltinDataTypeFolds) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$bits(int)", f)), 32);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$bits(byte)", f)), 8);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$bits(logic [7:0])", f)), 8);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$bits(logic [31:0])", f)), 32);
}

TEST(ConstEval, BitsLiteralIsResolvedWithoutEvaluatingValue) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$bits(12'bxxxxxxxxxxxx)", f)), 12);
}

TEST(ConstEval, BitsOfUnbasedUnsizedLiteralIsOne) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$bits('1)", f)), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$bits('x)", f)), 1);
}

TEST(BitsCallRestrictions, BitsOnQueueTypedefIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef byte qt[$];\n"
      "  int n;\n"
      "  initial n = $bits(qt);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'$bits' cannot be applied directly to dynamically sized type 'qt'", 4,
      "20.6.2"));
}

TEST(BitsCallRestrictions, BitsOnDynamicArrayTypedefIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef byte dt[];\n"
      "  int n;\n"
      "  initial n = $bits(dt);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'$bits' cannot be applied directly to dynamically sized type 'dt'", 4,
      "20.6.2"));
}

TEST(BitsCallRestrictions, BitsResultUsableInDataTypeDeclaration) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef bit [$bits(16'h0):1] MyBits;\n"
      "  MyBits b;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(BitsCallRestrictions, BitsResultUsableInVariableDeclaration) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  bit [$bits(16'h0):1] v;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(BitsCallRestrictions, BitsResultUsableInNetDeclaration) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  wire [$bits(16'h0):1] w;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(BitsCallRestrictions, BitsOnFixedTypedefIsLegal) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef logic [3:0] ft;\n"
      "  int n;\n"
      "  initial n = $bits(ft);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(BitsCallRestrictions, BitsEnclosingDynamicReturnFuncIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef byte qt[$];\n"
      "  function qt mkq(); return mkq; endfunction\n"
      "  int n;\n"
      "  initial n = $bits(mkq());\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'$bits' shall not enclose function 'mkq' whose "
                            "return type is dynamically sized",
                            5, "20.6.2"));
}

TEST(BitsCallRestrictions, BitsOnInterfaceClassObjectIsError) {
  ElabFixture f;
  Elaborate(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "  IC h;\n"
      "  int n;\n"
      "  initial n = $bits(h);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'$bits' shall not be applied to interface class object 'h'", 7,
      "20.6.2"));
}

TEST(BitsCallRestrictions, BitsOnQueueTypedefInAForStepIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef byte qt[$];\n"
      "  int n;\n"
      "  int i;\n"
      "  initial\n"
      "    for (i = 0; i < 1; n = $bits(qt))\n"
      "      n = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'$bits' cannot be applied directly to dynamically sized type 'qt'", 6,
      "20.6.2"));
}

TEST(BitsCallRestrictions,
     BitsOnQueueTypedefInAnAssertionPassStatementIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef byte qt[$];\n"
      "  int n;\n"
      "  logic ok;\n"
      "  initial assert (ok) n = $bits(qt);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'$bits' cannot be applied directly to dynamically sized type 'qt'", 5,
      "20.6.2"));
}

TEST(BitsCallRestrictions,
     BitsOnQueueTypedefInAnAssertionFailStatementIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef byte qt[$];\n"
      "  int c;\n"
      "  logic pass;\n"
      "  initial assert (pass) else c = $bits(qt);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'$bits' cannot be applied directly to dynamically sized type 'qt'", 5,
      "20.6.2"));
}

TEST(BitsCallRestrictions, BitsOnQueueTypedefInARandcaseItemIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef byte qt[$];\n"
      "  int total;\n"
      "  initial randcase 1: total = $bits(qt); endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'$bits' cannot be applied directly to dynamically sized type 'qt'", 4,
      "20.6.2"));
}

TEST(BitsCallRestrictions, BitsOnQueueTypedefInARandsequenceCodeBlockIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef byte qt[$];\n"
      "  int width;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { width = $bits(qt); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'$bits' cannot be applied directly to dynamically sized type 'qt'", 6,
      "20.6.2"));
}

TEST(BitsOfDeclaration, RangedParameterAnswersItsDeclaredWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [95:0] P = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "  localparam int W = $bits(P);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* w = FindParam(design, "m", "W");
  ASSERT_NE(w, nullptr);
  EXPECT_TRUE(w->is_resolved);
  EXPECT_EQ(w->resolved_value, 96);
}

TEST(BitsOfDeclaration, TypedParameterAnswersItsTypeWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int N = 5;\n"
      "  localparam int BN = $bits(N);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* bn = FindParam(design, "m", "BN");
  ASSERT_NE(bn, nullptr);
  EXPECT_TRUE(bn->is_resolved);
  EXPECT_EQ(bn->resolved_value, 32);
}

TEST(BitsOfDeclaration, ImplicitParameterAnswersItsValueWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam Q = 8'hFF;\n"
      "  localparam R = 100;\n"
      "  localparam int BQ = $bits(Q);\n"
      "  localparam int BR = $bits(R);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* bq = FindParam(design, "m", "BQ");
  ASSERT_NE(bq, nullptr);
  EXPECT_TRUE(bq->is_resolved);
  EXPECT_EQ(bq->resolved_value, 8);
  const auto* br = FindParam(design, "m", "BR");
  ASSERT_NE(br, nullptr);
  EXPECT_TRUE(br->is_resolved);
  EXPECT_EQ(br->resolved_value, 32);
}

TEST(BitsOfDeclaration, ParameterWidthSizesAVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [95:0] P = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "  logic [$bits(P)-1:0] v;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* v = FindVar(design, "m", "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 96u);
}

TEST(BitsOfDeclaration, VariableAnswersItsDeclaredWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] x;\n"
      "  localparam int BX = $bits(x);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* bx = FindParam(design, "m", "BX");
  ASSERT_NE(bx, nullptr);
  EXPECT_TRUE(bx->is_resolved);
  EXPECT_EQ(bx->resolved_value, 16);
}

TEST(BitsOfDeclaration, ImplicitParameterSetFromAWideParameterIsAsWide) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [95:0] P = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "  localparam S = P;\n"
      "  localparam int BS = $bits(S);\n"
      "  localparam int SH = S[95:64];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "BS"), 96);
  EXPECT_EQ(ParamValue(design, "SH"), 0x01234567);
}

TEST(BitsOfDeclaration, OperatorExpressionIsSizedBySelfDeterminedBitLength) {
  const std::vector<std::pair<std::string, int64_t>> kCases{
      {"B + B", 8},   {"B - B", 8},   {"B * B", 8},
      {"B / B", 8},   {"B % B", 8},   {"B & B", 8},
      {"B | B", 8},   {"B ^ B", 8},   {"B ^~ B", 8},
      {"B ~^ B", 8},  {"B + 1", 32},  {"B << 4", 8},
      {"B <<< 4", 8}, {"B >> 4", 8},  {"B >>> 4", 8},
      {"B ** 2", 8},  {"B < B", 1},   {"B > B", 1},
      {"B <= B", 1},  {"B >= B", 1},  {"B == B", 1},
      {"B != B", 1},  {"B === B", 1}, {"B !== B", 1},
      {"B ==? B", 1}, {"B !=? B", 1}, {"B && B", 1},
      {"B || B", 1},  {"B -> B", 1},  {"B <-> B", 1},
      {"+B", 8},      {"-B", 8},      {"~B", 8},
      {"&B", 1},      {"~&B", 1},     {"|B", 1},
      {"~|B", 1},     {"^B", 1},      {"~^B", 1},
      {"^~B", 1},     {"!B", 1},      {"B ? B : 16'h1", 16}};
  std::string src =
      "module m;\n"
      "  localparam logic [7:0] B = 8'hFF;\n";
  for (size_t i = 0; i < kCases.size(); ++i) {
    src += "  localparam int W" + std::to_string(i) + " = $bits(" +
           kCases[i].first + ");\n";
  }
  src += "endmodule\n";
  ElabFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  for (size_t i = 0; i < kCases.size(); ++i) {
    EXPECT_EQ(ParamValue(design, "W" + std::to_string(i)), kCases[i].second)
        << kCases[i].first;
  }
}

TEST(BitsOfDeclaration, OperatorWithNoSelfDeterminedBitLengthIsLeftUnsized) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [7:0] B = 8'hFF;\n"
      "  localparam int W = $bits(B |-> B);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the property operator '|->' joins the operands "
                            "of an ordinary expression",
                            3, "A.8.6"));
  EXPECT_TRUE(design == nullptr || ParamUnresolved(design, "W"));
}

TEST(BitsOfDeclaration, ParameterNameReadsAtItsDeclaredWidthAndSign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam byte B = 300;\n"
      "  localparam bit [3:0] Y = -1;\n"
      "  parameter signed SG = -3;\n"
      "  localparam int RB = B;\n"
      "  localparam int RY = Y;\n"
      "  localparam int RS = SG;\n"
      "  localparam int BSG = $bits(SG);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "RB"), 44);
  EXPECT_EQ(ParamValue(design, "RY"), 15);
  EXPECT_EQ(ParamValue(design, "RS"), -3);
  EXPECT_EQ(ParamValue(design, "BSG"), 32);
}

TEST(BitsOfDeclaration, FormalNamedAsAParameterIsNotCutToItsWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam byte K = 3;\n"
      "  function automatic int f(input int K);\n"
      "    return K;\n"
      "  endfunction\n"
      "  localparam int R = f(300);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "R"), 300);
}

TEST(BitsOfDeclaration, ImplicitParameterSetFromAnEnumConstantReadsAsInt) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef enum {A0, A1} e_t;\n"
      "  localparam E = A1;\n"
      "  localparam int X = E + A1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "X"), 2);
}

TEST(BitsOfDeclaration, SelfReferentialWideParameterTerminates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "localparam logic [95:0] P = 96'h1;\n"
      "module m;\n"
      "  localparam logic [95:0] P = P + 1;\n"
      "  localparam int H = P[95:64];\n"
      "  localparam int L = P[31:0];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(ParamValue(design, "H"), 0);
  EXPECT_EQ(ParamValue(design, "L"), 2);
}

TEST(BitsOfDeclaration, WideLiteralOfEachBaseCarriesItsHighBits) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [95:0] PL = 96'h0123_4567_89ab_cdef_0011_2233;\n"
      "  localparam int PLH = PL[95:64];\n"
      "  localparam logic [79:0] PB = 80'b"
      "1000000000000000000000000000000000000000"
      "0000000000000000000000000000000000000001;\n"
      "  localparam int PBH = PB[79:64];\n"
      "  localparam logic [71:0] PO = 72'O400000000000000000000001;\n"
      "  localparam int POH = PO[71:64];\n"
      "  localparam logic [79:0] PD = 80'd604462909807314587353089;\n"
      "  localparam int PDH = PD[79:64];\n"
      "  localparam logic [95:0] PX = 96'h0123_4567_89AB_CDEF_0011_22x3;\n"
      "  localparam int PXH = PX[95:64];\n"
      "  localparam logic [127:0] PW ="
      " 128'hFEDC_BA98_7654_3210_0123_4567_89AB_CDEF;\n"
      "  localparam int PWH = PW[127:96];\n"
      "  localparam int PWM = PW[95:64];\n"
      "  localparam logic [95:0] PZ = 96'h1;\n"
      "  localparam int PZH = PZ[95:64];\n"
      "  localparam int PZL = PZ[7:0];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "PLH"), 0x01234567);
  EXPECT_EQ(ParamValue(design, "PBH"), 0x8000);
  EXPECT_EQ(ParamValue(design, "POH"), 0x80);
  EXPECT_EQ(ParamValue(design, "PDH"), 0x8000);
  EXPECT_EQ(ParamValue(design, "PXH"), 0x00012345);
  EXPECT_EQ(ParamValue(design, "PWH"), 0xFEDCBA98);
  EXPECT_EQ(ParamValue(design, "PWM"), 0x76543210);
  EXPECT_EQ(ParamValue(design, "PZH"), 0);
  EXPECT_EQ(ParamValue(design, "PZL"), 1);
}

TEST(BitsOfDeclaration, BitSelectAboveSixtyFourAndBelowZero) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [95:0] P = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "  localparam int B64 = P[64];\n"
      "  localparam int B67 = P[67];\n"
      "  localparam int B95 = P[95];\n"
      "  localparam int LOW = P[3:-4];\n"
      "  localparam int NEG = P[-1];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(ParamValue(design, "B64"), 1);
  EXPECT_EQ(ParamValue(design, "B67"), 0);
  EXPECT_EQ(ParamValue(design, "B95"), 0);
  EXPECT_TRUE(ParamUnresolved(design, "LOW"));
  EXPECT_TRUE(ParamUnresolved(design, "NEG"));
}

TEST(BitsOfDeclaration, ShiftAndBitwiseOperatorsWorkAcrossTheWideValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [95:0] P = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "  localparam logic [95:0] M = 96'hF0F0_F0F0_F0F0_F0F0_F0F0_F0F0;\n"
      "  localparam logic signed [95:0] PS = "
      "96'sh8000_0000_0000_0000_0000_0001;\n"
      "  localparam logic signed [95:0] PP = "
      "96'sh0123_4567_89AB_CDEF_0011_2233;\n"
      "  localparam logic [95:0] A = P & M;\n"
      "  localparam int AH = A[95:64];\n"
      "  localparam int AL = A[31:0];\n"
      "  localparam logic [95:0] O = P | M;\n"
      "  localparam int OH = O[95:64];\n"
      "  localparam logic [95:0] X = P ^ M;\n"
      "  localparam int XH = X[95:64];\n"
      "  localparam logic [95:0] N1 = P ~^ M;\n"
      "  localparam int N1H = N1[95:64];\n"
      "  localparam logic [95:0] N2 = P ^~ M;\n"
      "  localparam int N2H = N2[95:64];\n"
      "  localparam logic [95:0] SL = P << 4;\n"
      "  localparam int SLH = SL[95:64];\n"
      "  localparam int SLL = SL[31:0];\n"
      "  localparam logic [95:0] SW = P <<< 64;\n"
      "  localparam int SWH = SW[95:64];\n"
      "  localparam int SWL = SW[31:0];\n"
      "  localparam logic [95:0] SR = P >> 4;\n"
      "  localparam int SRH = SR[95:64];\n"
      "  localparam int SRL = SR[31:0];\n"
      "  localparam logic [95:0] SA = P >>> 4;\n"
      "  localparam int SAH = SA[95:64];\n"
      "  localparam logic signed [95:0] SS = PS >>> 4;\n"
      "  localparam int SSH = SS[95:64];\n"
      "  localparam logic signed [95:0] SQ = PP >>> 4;\n"
      "  localparam int SQH = SQ[95:64];\n"
      "  localparam logic signed [95:0] SM = PS & M;\n"
      "  localparam int SMH = SM[95:64];\n"
      "  localparam logic [95:0] I = P + 1;\n"
      "  localparam int IL = I[31:0];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "AH"), 0x00204060);
  EXPECT_EQ(ParamValue(design, "AL"), 0x00102030);
  EXPECT_EQ(ParamValue(design, "OH"), 0xF1F3F5F7);
  EXPECT_EQ(ParamValue(design, "XH"), 0xF1D3B597);
  EXPECT_EQ(ParamValue(design, "N1H"), 0x0E2C4A68);
  EXPECT_EQ(ParamValue(design, "N2H"), 0x0E2C4A68);
  EXPECT_EQ(ParamValue(design, "SLH"), 0x12345678);
  EXPECT_EQ(ParamValue(design, "SLL"), 0x01122330);
  EXPECT_EQ(ParamValue(design, "SWH"), 0x00112233);
  EXPECT_EQ(ParamValue(design, "SWL"), 0);
  EXPECT_EQ(ParamValue(design, "SRH"), 0x00123456);
  EXPECT_EQ(ParamValue(design, "SRL"), 0xF0011223);
  EXPECT_EQ(ParamValue(design, "SAH"), 0x00123456);
  EXPECT_EQ(ParamValue(design, "SSH"), 0xF8000000);
  EXPECT_EQ(ParamValue(design, "SQH"), 0x00123456);
  EXPECT_EQ(ParamValue(design, "SMH"), 0x80000000);
  EXPECT_EQ(ParamValue(design, "IL"), 0x00112234);
}

TEST(BitsOfDeclaration, LiteralOverrideReadsAboveBitSixtyFour) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module c #(parameter logic [95:0] P = 96'h0);\n"
      "  localparam int H = P[95:64];\n"
      "  localparam int L = P[31:0];\n"
      "endmodule\n"
      "module t;\n"
      "  localparam logic [95:0] PP = 96'h0123_4567_89AB_CDEF_0011_2233;\n"
      "  c #(.P(96'h0123_4567_89AB_CDEF_0011_2233)) u1();\n"
      "  c #(.P(PP)) u2();\n"
      "endmodule\n",
      f, "t");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto& children = design->top_modules[0]->children;
  ASSERT_EQ(children.size(), 2u);
  auto value = [](const RtlirModule* c, std::string_view name) {
    for (const auto& p : c->params)
      if (p.name == name) return p.resolved_value;
    return int64_t{-1};
  };
  EXPECT_EQ(value(children[0].resolved, "H"), 0x01234567);
  EXPECT_EQ(value(children[0].resolved, "L"), 0x00112233);
  EXPECT_EQ(value(children[1].resolved, "H"), 0x01234567);
  EXPECT_EQ(value(children[1].resolved, "L"), 0x00112233);
}

TEST(BitsOfDeclaration, NetAndUnpackedArrayAnswerTheirBits) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr[4];\n"
      "  logic [7:0] grid[2][3];\n"
      "  wire [7:0] w[3];\n"
      "  wire [3:0] v;\n"
      "  localparam int BA = $bits(arr);\n"
      "  localparam int BG = $bits(grid);\n"
      "  localparam int BW = $bits(w);\n"
      "  localparam int BV = $bits(v);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(ParamValue(design, "BA"), 32);
  EXPECT_EQ(ParamValue(design, "BG"), 48);
  EXPECT_EQ(ParamValue(design, "BW"), 24);
  EXPECT_EQ(ParamValue(design, "BV"), 4);
  const auto* w = FindNet(design, "m", "w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->num_unpacked_dims, 1u);
  EXPECT_EQ(w->unpacked_dim_sizes, std::vector<uint32_t>{3});
  const auto* v = FindNet(design, "m", "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->num_unpacked_dims, 0u);
}

TEST(BitsOfDeclaration, TypedefNameAnswersItsTypeWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef logic [11:0] my_t;\n"
      "  localparam int BT = $bits(my_t);\n"
      "  typedef struct packed { logic [3:0] a; logic [7:0] b; } s_t;\n"
      "  localparam int BS = $bits(s_t);\n"
      "  typedef s_t alias_t;\n"
      "  localparam int BA = $bits(alias_t);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "BT"), 12);
  EXPECT_EQ(ParamValue(design, "BS"), 12);
  EXPECT_EQ(ParamValue(design, "BA"), 12);
}

}  // namespace
