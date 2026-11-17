#include <gtest/gtest.h>

#include <cstdint>
#include <optional>
#include <string_view>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "fixture_evaluator.h"
#include "helpers_param_value.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

int64_t ResolvedParam(RtlirDesign* design, std::string_view name) {
  for (auto& p : design->top_modules[0]->params) {
    if (p.name == name) {
      EXPECT_TRUE(p.is_resolved);
      return p.resolved_value;
    }
  }
  ADD_FAILURE() << "parameter not found: " << name;
  return -1;
}

TEST(ConstEval, Countones) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$countones(8'b10110010)", f)), 4);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$countones(8'b00000000)", f)), 0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$countones(8'b11111111)", f)), 8);
}

TEST(ConstEval, Onehot) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$onehot(8'b00000001)", f)), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$onehot(8'b00001000)", f)), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$onehot(8'b00000000)", f)), 0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$onehot(8'b00010010)", f)), 0);
}

TEST(ConstEval, Onehot0) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$onehot0(8'b00000001)", f)), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$onehot0(8'b00000000)", f)), 1);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$onehot0(8'b00010010)", f)), 0);
}

TEST(ConstEval, IsunknownConstantInt) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$isunknown(8'b10110010)", f)), 0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$isunknown(8'h00)", f)), 0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$isunknown(32'hFFFFFFFF)", f)), 0);
}

TEST(ConstEval, CountbitsConstantIntOnesAndZeros) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$countbits(8'b10110010, 1'b1)", f)), 4);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$countbits(8'b10110010, 1'b0)", f)), 4);
  EXPECT_EQ(
      ConstEvalInt(ParseExprFrom("$countbits(8'b10110010, 1'b1, 1'b0)", f)), 8);
}

TEST(ConstEval, CountbitsConstantIntDedupAndXZ) {
  EvalFixture f;
  EXPECT_EQ(
      ConstEvalInt(ParseExprFrom("$countbits(8'b10110010, 1'b1, 1'b1)", f)), 4);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$countbits(8'b10110010, 1'bx)", f)), 0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$countbits(8'b10110010, 1'bz)", f)), 0);
}

TEST(ConstEval, BitVectorFunctionsFoldWithParameterArgument) {
  EvalFixture f;
  ScopeMap scope = {{"P", 0xA5}};
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$countones(P)", f), scope), 4);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$countbits(P, 1'b1)", f), scope), 4);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$onehot(P)", f), scope), 0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$onehot0(P)", f), scope), 0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$countbits(P, 1'b0)", f), scope), 28);
}

TEST(ConstEval, BitVectorFunctionDoesNotFoldWithNonConstantArgument) {
  EvalFixture f;
  ScopeMap scope = {{"P", 0xA5}};
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$countones(UNKNOWN)", f), scope),
            std::nullopt);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$countbits(UNKNOWN, 1'b1)", f), scope),
            std::nullopt);
}

TEST(ConstEval, BitVectorFunctionsFoldWithParameterArgumentEndToEnd) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter logic [7:0] MASK = 8'hA5;\n"
      "  localparam int ONES = $countones(MASK);\n"
      "  localparam int CB = $countbits(MASK, 1'b1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "ONES"), 4);
  EXPECT_EQ(ResolvedParam(design, "CB"), 4);
}

TEST(ConstEval, BitVectorFunctionsFoldWithLocalparamArgumentEndToEnd) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam logic [7:0] MASK = 8'hA5;\n"
      "  localparam int OH0 = $onehot0(MASK);\n"
      "  localparam int UNK = $isunknown(MASK);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ResolvedParam(design, "OH0"), 0);
  EXPECT_EQ(ResolvedParam(design, "UNK"), 0);
}

TEST(BitVectorFunctionArgs, RejectsRealExpressionArgument) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real r;\n"
      "  int c;\n"
      "  initial c = $countones(r);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "'$countones' works on bit-stream values, and its "
                    "expression argument's type is not a bit-stream type",
                    4, "20.9"));
}

TEST(BitVectorFunctionArgs, RejectsRealArgumentToIsunknown) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real r;\n"
      "  logic u;\n"
      "  initial u = $isunknown(r);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "'$isunknown' works on bit-stream values, and its "
                    "expression argument's type is not a bit-stream type",
                    4, "20.9"));
}

TEST(BitVectorFunctionArgs, RejectsCountbitsWithoutControlBit) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] v;\n"
      "  int c;\n"
      "  initial c = $countbits(v);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'$countbits' requires at least one control_bit argument", 4, "20.9"));
}

TEST(BitVectorFunctionArgs, AcceptsIntegralExpressionArgument) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] v;\n"
      "  int c;\n"
      "  initial c = $countones(v);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(BitVectorFunctionArgs, RejectsRealArgumentInAForStep) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real rv;\n"
      "  int i;\n"
      "  initial\n"
      "    for (i = 0; i < 1; i = $countones(rv))\n"
      "      i = i + 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "'$countones' works on bit-stream values, and its "
                    "expression argument's type is not a bit-stream type",
                    5, "20.9"));
}

TEST(BitVectorFunctionArgs, RejectsRealArgumentInAnAssertionPassStatement) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real amp;\n"
      "  logic hot;\n"
      "  logic ready;\n"
      "  initial assert (ready) hot = $onehot(amp);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "'$onehot' works on bit-stream values, and its expression "
                    "argument's type is not a bit-stream type",
                    5, "20.9"));
}

TEST(BitVectorFunctionArgs, RejectsRealArgumentInAnAssertionFailStatement) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real gain;\n"
      "  logic clear;\n"
      "  logic go;\n"
      "  initial assert (go) else clear = $onehot0(gain);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "'$onehot0' works on bit-stream values, and its expression "
                    "argument's type is not a bit-stream type",
                    5, "20.9"));
}

TEST(BitVectorFunctionArgs, RejectsRealArgumentInARandcaseItem) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real drift;\n"
      "  logic unk;\n"
      "  initial randcase 2: unk = $isunknown(drift); endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "'$isunknown' works on bit-stream values, and its "
                    "expression argument's type is not a bit-stream type",
                    4, "20.9"));
}

TEST(BitVectorFunctionArgs, RejectsRealArgumentInARandsequenceCodeBlock) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real slope;\n"
      "  int bits;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { bits = $countbits(slope, 1'b1); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "'$countbits' works on bit-stream values, and its "
                    "expression argument's type is not a bit-stream type",
                    6, "20.9"));
}

TEST(BitVectorFunctionArgs,
     AcceptsAVirtualInterfaceMemberSelectAsTheExpressionArgument) {
  ElabFixture f;
  EXPECT_TRUE(
      ElabOk("interface I;\n"
             "  logic sig;\n"
             "endinterface\n"
             "module m;\n"
             "  virtual interface I vif;\n"
             "  logic u;\n"
             "  initial u = $isunknown(vif.sig);\n"
             "endmodule\n",
             f));
}

TEST(BitVectorFunctionElab, AVariableOfANonBitStreamTypeIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  shortreal sr;\n"
      "  realtime rt;\n"
      "  chandle ch;\n"
      "  event ev;\n"
      "  real ra[2];\n"
      "  bit r[4];\n"
      "  initial begin\n"
      "    r[0] = $onehot(sr);\n"
      "    r[1] = $onehot(rt);\n"
      "    r[2] = $isunknown(ch);\n"
      "    r[3] = $onehot0(ev);\n"
      "    r[0] = $isunknown(ra);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "'$onehot' works on bit-stream values, and its expression "
                    "argument's type is not a bit-stream type",
                    9, "20.9"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "'$onehot' works on bit-stream values, and its expression "
                    "argument's type is not a bit-stream type",
                    10, "20.9"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "'$isunknown' works on bit-stream values, and its "
                    "expression argument's type is not a bit-stream type",
                    11, "20.9"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "'$onehot0' works on bit-stream values, and its expression "
                    "argument's type is not a bit-stream type",
                    12, "20.9"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "'$isunknown' works on bit-stream values, and its "
                    "expression argument's type is not a bit-stream type",
                    13, "20.9"));
  EXPECT_EQ(f.diag.ErrorCount(), 5u);
}

TEST(BitVectorFunctionElab,
     DISABLED_ARealLiteralOrAStructWithARealMemberIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef struct {int a; real b;} sr_t;\n"
      "  sr_t s;\n"
      "  int n, m;\n"
      "  initial begin\n"
      "    n = $countones(1.5);\n"
      "    m = $countbits(s, 1);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "'$countones' works on bit-stream values, and its "
                    "expression argument's type is not a bit-stream type",
                    6, "20.9"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "'$countbits' works on bit-stream values, and its "
                    "expression argument's type is not a bit-stream type",
                    7, "20.9"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(BitVectorFunctionElab, AnIntegralUnpackedStructAndAStringAreAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct {int a; logic [3:0] b;} s_t;\n"
             "  s_t s;\n"
             "  string str;\n"
             "  int n, m;\n"
             "  initial begin\n"
             "    n = $countones(s);\n"
             "    m = $countbits(str, 0);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(BitVectorFunctionElab, ACountbitsCallWithNoArgumentIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int n;\n"
      "  initial n = $countbits();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'$countbits' requires at least one control_bit argument", 3, "20.9"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(BitVectorFunctionElab, EachOneOperandFunctionWithOneArgumentIsAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic [3:0] c;\n"
             "  int n;\n"
             "  bit a, b, d;\n"
             "  initial begin\n"
             "    n = $countones(c);\n"
             "    a = $onehot(c);\n"
             "    b = $onehot0(c);\n"
             "    d = $isunknown(c);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(BitVectorFunctionElab,
     DISABLED_AOneOperandFunctionWithNoneOrTwoArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic [3:0] c;\n"
      "  int r[8];\n"
      "  initial begin\n"
      "    r[0] = $countones();\n"
      "    r[1] = $onehot();\n"
      "    r[2] = $onehot0();\n"
      "    r[3] = $isunknown();\n"
      "    r[4] = $countones(c, c);\n"
      "    r[5] = $onehot(c, c);\n"
      "    r[6] = $onehot0(c, c);\n"
      "    r[7] = $isunknown(c, 1'b1);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'$countones' takes exactly one argument", 5,
                            "20.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'$onehot' takes exactly one argument", 6, "20.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'$onehot0' takes exactly one argument", 7,
                            "20.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'$isunknown' takes exactly one argument", 8,
                            "20.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'$countones' takes exactly one argument", 9,
                            "20.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'$onehot' takes exactly one argument", 10,
                            "20.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'$onehot0' takes exactly one argument", 11,
                            "20.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'$isunknown' takes exactly one argument", 12,
                            "20.9"));
  EXPECT_EQ(f.diag.ErrorCount(), 8u);
}

TEST(BitVectorFunctionElab,
     ACallWithConstantArgumentsFoldsWhereAConstantIsRequired) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package pk;\n"
      "  localparam int PO = $countones(8'hF1);\n"
      "endpackage\n"
      "module m;\n"
      "  localparam logic [7:0] P = 8'h0F;\n"
      "  logic [$countones(P) - 1 : 0] v;\n"
      "  localparam int W = $bits(v);\n"
      "  localparam int L = $countbits(8'b1010_0000, 2'b10);\n"
      "  localparam int Q = pk::PO;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "W"), 4);
  EXPECT_EQ(ParamValue(design, "L"), 6);
  EXPECT_EQ(ParamValue(design, "Q"), 5);
}

TEST(BitVectorFunctionElab, DISABLED_AConstantOperandWithXOrZBitsFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int X = $isunknown(4'b10x1);\n"
      "  localparam int Z = $countbits(4'bz0x1, 1'bz);\n"
      "  localparam int K = $isunknown(4'b1001);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "X"), 1);
  EXPECT_EQ(ParamValue(design, "Z"), 1);
  EXPECT_EQ(ParamValue(design, "K"), 0);
}

}  // namespace
