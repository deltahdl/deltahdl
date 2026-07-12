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

// §11.4.10: logical and arithmetic right shift fill vacated high bits
// differently. A negative constant exposes the split during constant folding:
// >>> sign-fills (the value stays negative), while >> zero-fills (the value
// becomes a large nonnegative magnitude). Positive operands cannot tell the two
// operators apart, so this is the case the elaborator-stage checks must add.
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

// §11.4.10 also governs the shift when its operand is a constant expression
// folded at elaboration. A parameter reference resolves through a different
// const-eval path than a literal, so the left-shift rule is exercised here with
// the operand produced by a `parameter` declaration: 3 << 2 folds to 12 with
// the low bits zero-filled.
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

// The logical right-shift rule at const-fold time with a localparam operand:
// 16 >> 2 folds to 4, the high bits vacated by the shift filled with zeros. The
// localparam operand takes the identifier-resolution path rather than the
// literal path used by the sibling ConstEval cases.
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

// The arithmetic right shift sign-fills at const-fold time when the operand is
// a signed constant. Building the operand from a signed parameter declaration
// (rather than a negative literal) drives the signed-result path: -8 >>> 1
// folds to -4, whereas a logical >> on the same value would fold to a large
// positive magnitude.
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
