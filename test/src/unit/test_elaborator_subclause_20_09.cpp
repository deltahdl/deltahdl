#include <gtest/gtest.h>

#include <cstdint>
#include <optional>
#include <string_view>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "fixture_evaluator.h"
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

}  // namespace
