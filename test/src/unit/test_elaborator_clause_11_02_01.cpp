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
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  parameter int P = 3 + 4;\n"
      "endmodule\n"));
}

TEST(ConstantExpressionElaboration, DependentParamsElaborate) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  parameter int WIDTH = 8;\n"
      "  parameter int DEPTH = 2 ** WIDTH;\n"
      "endmodule\n"));
}

TEST(ConstantExpressionElaboration, ConstantSysFuncInParamElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  parameter int P = $clog2(256);\n"
      "endmodule\n"));
}

TEST(ConstantExpressionElaboration, ConcatenationInParamElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  parameter logic [7:0] P = {4'd3, 4'd5};\n"
      "endmodule\n"));
}

TEST(ConstantExpressionElaboration, ReplicationInParamElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  parameter logic [3:0] P = {4{1'b1}};\n"
      "endmodule\n"));
}

TEST(ConstantExpressionElaboration, UnaryExprInParamElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  parameter int P = -42;\n"
      "endmodule\n"));
}

TEST(ConstantExpressionElaboration, StringLiteralInParamElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  parameter string S = \"hello\";\n"
      "endmodule\n"));
}

TEST(ConstantExpressionElaboration, NestedSysFuncInParamElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
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

}  // namespace
