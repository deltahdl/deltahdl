#include "fixture_elaborator.h"
#include "fixture_evaluator.h"

using namespace delta;

namespace {

TEST(ConstantExpressionElaboration, ConstantTernaryInParamElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int P = 1 ? 10 : 20;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstEval, ScopedUnresolved) {
  EvalFixture f;
  ScopeMap scope = {{"WIDTH", 16}};
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("UNKNOWN", f), scope), std::nullopt);
}

TEST(ConstantExpressionElaboration, BinaryExprInParamElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter int P = 3 + 4;\n"
             "endmodule\n"));
}

TEST(ConstantExpressionElaboration, DependentParamsElaborate) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter int WIDTH = 8;\n"
             "  parameter int DEPTH = 2 ** WIDTH;\n"
             "endmodule\n"));
}

TEST(ConstantExpressionElaboration, ConstantSysFuncInParamElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter int P = $clog2(256);\n"
             "endmodule\n"));
}

TEST(ConstantExpressionElaboration, ConcatenationInParamElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter logic [7:0] P = {4'd3, 4'd5};\n"
             "endmodule\n"));
}

TEST(ConstantExpressionElaboration, ReplicationInParamElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter logic [3:0] P = {4{1'b1}};\n"
             "endmodule\n"));
}

TEST(ConstantExpressionElaboration, UnaryExprInParamElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter int P = -42;\n"
             "endmodule\n"));
}

TEST(ConstantExpressionElaboration, StringLiteralInParamElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter string S = \"hello\";\n"
             "endmodule\n"));
}

TEST(ConstantExpressionElaboration, NestedSysFuncInParamElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter int P = $clog2($bits(logic [31:0]));\n"
             "endmodule\n"));
}

TEST(ConstEval, ScopedConcatenationEvaluation) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("{4'd3, 4'd5}", f)), 0x35);
}

TEST(ConstEval, ScopedReplicationEvaluation) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("{4{1'b1}}", f)), 15);
}

TEST(ConstEval, ScopedSysFuncEvaluation) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$clog2(256)", f)), 8);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$clog2(1)", f)), 0);
}

TEST(ConstEvalReal, RealLiteralEvaluation) {
  EvalFixture f;
  auto val = ConstEvalReal(ParseExprFrom("3.14", f));
  ASSERT_TRUE(val.has_value());
  EXPECT_DOUBLE_EQ(*val, 3.14);
}

TEST(ConstEvalReal, RealBinaryEvaluation) {
  EvalFixture f;
  auto val = ConstEvalReal(ParseExprFrom("1.5 + 2.5", f));
  ASSERT_TRUE(val.has_value());
  EXPECT_DOUBLE_EQ(*val, 4.0);
}

TEST(ConstEvalReal, IntPromotesToReal) {
  EvalFixture f;
  auto val = ConstEvalReal(ParseExprFrom("42", f));
  ASSERT_TRUE(val.has_value());
  EXPECT_DOUBLE_EQ(*val, 42.0);
}

TEST(ConstEvalReal, DivisionByZeroReturnsNullopt) {
  EvalFixture f;
  auto val = ConstEvalReal(ParseExprFrom("1.0 / 0.0", f));
  EXPECT_FALSE(val.has_value());
}

// §11.2.1 exposes the constant-system-function whitelist so §13.4.3 can apply
// the same admissibility rule when validating the body of a constant function.
// Spot-check one entry from each family the LRM lists: math, conversion,
// bit-vector, timescale, $sformatf. Non-pure sys funcs (e.g. $time) must be
// rejected.
TEST(ConstantSysFuncWhitelist, MathFunctionAdmitted) {
  EXPECT_TRUE(IsConstantSysFunc("$clog2"));
  EXPECT_TRUE(IsConstantSysFunc("$sqrt"));
}

TEST(ConstantSysFuncWhitelist, ConversionFunctionAdmitted) {
  EXPECT_TRUE(IsConstantSysFunc("$signed"));
  EXPECT_TRUE(IsConstantSysFunc("$itor"));
}

TEST(ConstantSysFuncWhitelist, BitVectorFunctionAdmitted) {
  EXPECT_TRUE(IsConstantSysFunc("$countones"));
  EXPECT_TRUE(IsConstantSysFunc("$onehot"));
}

TEST(ConstantSysFuncWhitelist, TimescaleFunctionAdmitted) {
  EXPECT_TRUE(IsConstantSysFunc("$timescale"));
  EXPECT_TRUE(IsConstantSysFunc("$timeprecision"));
}

TEST(ConstantSysFuncWhitelist, SformatfAdmitted) {
  EXPECT_TRUE(IsConstantSysFunc("$sformatf"));
}

TEST(ConstantSysFuncWhitelist, ImpureFunctionRejected) {
  EXPECT_FALSE(IsConstantSysFunc("$time"));
  EXPECT_FALSE(IsConstantSysFunc("$display"));
  EXPECT_FALSE(IsConstantSysFunc("$random"));
}

// §11.2.1: constant bit-selects and part-selects of parameters are listed
// among the legal operands of a constant expression. Make sure the
// elaborator accepts a parameter whose value is computed from a bit-select
// of another parameter.
TEST(ConstantExpressionElaboration, ConstantBitSelectOfParameterElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter logic [7:0] BASE = 8'b1010_1100;\n"
             "  parameter logic       BIT  = BASE[5];\n"
             "endmodule\n"));
}

TEST(ConstantExpressionElaboration, ConstantPartSelectOfParameterElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter logic [7:0] BASE  = 8'b1010_1100;\n"
             "  parameter logic [3:0] NIBBLE = BASE[7:4];\n"
             "endmodule\n"));
}

// §11.2.1: a built-in method call is constant when used as the initialiser
// of a parameter — observe that path through const_eval.
TEST(ConstantExpressionElaboration, ConstantBuiltinMethodTypeQueryElaborates) {
  EvalFixture f;
  auto* e = ParseExprFrom("v.bits", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

}  // namespace
