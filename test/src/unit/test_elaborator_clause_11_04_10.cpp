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

}  // namespace
