#include <gtest/gtest.h>

#include "elaborator/const_eval.h"
#include "fixture_elaborator.h"
#include "fixture_evaluator.h"

using namespace delta;

namespace {

TEST(ConstEval, Shifts) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("1 << 4", f)), 16);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("16 >> 2", f)), 4);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("1 <<< 4", f)), 16);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("16 >>> 2", f)), 4);
}

TEST(OperatorElaboration, BinaryArithShiftRightElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd128 >>> 2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, BinaryArithShiftLeftElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd1 <<< 3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstEval, ShiftByZero) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("42 << 0", f)), 42);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("42 >> 0", f)), 42);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("42 <<< 0", f)), 42);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("42 >>> 0", f)), 42);
}

TEST(ConstEval, RightShiftSignedVersusLogicalFill) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("(-8) >>> 1", f)), -4);
  auto logical = ConstEvalInt(ParseExprFrom("(-8) >> 1", f));
  ASSERT_TRUE(logical.has_value());
  if (!logical.has_value()) return;
  const auto kLogicalValue = *logical;
  EXPECT_NE(kLogicalValue, -4);
  EXPECT_GT(kLogicalValue, 0);
}

TEST(ConstEval, LeftShiftAndArithLeftShiftEquivalent) {
  EvalFixture f;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("7 << 3", f)),
            ConstEvalInt(ParseExprFrom("7 <<< 3", f)));
}

TEST(OperatorElaboration, LogicalLeftShiftElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd1 << 4;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorElaboration, LogicalRightShiftElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd128 >> 3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConstEval, LeftShiftOfParameterFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter P = 3;\n"
      "  localparam Q = P << 2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 2u);
  auto& q = design->top_modules[0]->params[1];
  EXPECT_EQ(q.name, "Q");
  EXPECT_EQ(q.resolved_value, 12);
}

TEST(ConstEval, LogicalRightShiftOfLocalparamFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam A = 16;\n"
      "  localparam B = A >> 2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 2u);
  auto& b = design->top_modules[0]->params[1];
  EXPECT_EQ(b.name, "B");
  EXPECT_EQ(b.resolved_value, 4);
}

TEST(ConstEval, ArithRightShiftOfSignedParameterSignFills) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter signed P = -8;\n"
      "  localparam Q = P >>> 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_GE(design->top_modules[0]->params.size(), 2u);
  auto& q = design->top_modules[0]->params[1];
  EXPECT_EQ(q.name, "Q");
  EXPECT_EQ(q.resolved_value, -4);
}

}  // namespace
