#include "fixture_evaluator.h"

using namespace delta;

namespace {

TEST(ConstEvalSteps, IntegerOperandPromotedToRealInMixedAddition) {
  EvalFixture f;
  auto* e = ParseExprFrom("2 + 3.5", f);
  auto val = ConstEvalReal(e);
  ASSERT_TRUE(val.has_value());
  EXPECT_DOUBLE_EQ(val.value_or(0.0), 5.5);
}

TEST(ConstEvalSteps, IntegerOperandPromotedToRealInMixedMultiplication) {
  EvalFixture f;
  auto* e = ParseExprFrom("3 * 2.5", f);
  auto val = ConstEvalReal(e);
  ASSERT_TRUE(val.has_value());
  EXPECT_DOUBLE_EQ(val.value_or(0.0), 7.5);
}

TEST(ConstEvalSteps, RealOperandPromotedThroughUnaryNegation) {
  EvalFixture f;
  auto* e = ParseExprFrom("-4.25", f);
  auto val = ConstEvalReal(e);
  ASSERT_TRUE(val.has_value());
  EXPECT_DOUBLE_EQ(val.value_or(0.0), -4.25);
}

TEST(ConstEvalSteps, IntegerOperandUnderUnaryMinusConvertsToRealValue) {
  EvalFixture f;
  auto* e = ParseExprFrom("-5", f);
  auto val = ConstEvalReal(e);
  ASSERT_TRUE(val.has_value());
  EXPECT_DOUBLE_EQ(val.value_or(0.0), -5.0);
}

TEST(ConstEvalSteps, IntegerDividendConvertsToRealForRealDivision) {
  EvalFixture f;
  auto* e = ParseExprFrom("10 / 4.0", f);
  auto val = ConstEvalReal(e);
  ASSERT_TRUE(val.has_value());
  EXPECT_DOUBLE_EQ(val.value_or(0.0), 2.5);
}

TEST(ConstEvalSteps, SignedNegativeLiteralSignExtendsThroughEvaluation) {
  EvalFixture f;
  auto* e = ParseExprFrom("-4'sd1 + 8'sd0", f);
  auto val = ConstEvalInt(e);
  ASSERT_TRUE(val.has_value());
  EXPECT_EQ(val.value_or(0), -1);
}

TEST(ConstEvalSteps, UnsignedLiteralZeroExtendsThroughEvaluation) {
  EvalFixture f;
  auto* e = ParseExprFrom("4'hF + 8'h00", f);
  auto val = ConstEvalInt(e);
  ASSERT_TRUE(val.has_value());
  EXPECT_EQ(val.value_or(-1), 15);
}

TEST(ConstEvalSteps, SignedRelationalConstantExpressionMutuallyDetermined) {
  // §11.8.2 exception 2: relational operands mutually determine a shared width
  // and sign-extend when signed, producing a 1-bit result. The narrow -1 must
  // sign-extend to compare as negative against the wider operand.
  EvalFixture f;
  auto* e = ParseExprFrom("-4'sd1 < 8'sd5", f);
  auto val = ConstEvalInt(e);
  ASSERT_TRUE(val.has_value());
  // -1 < 5 is true; a zero-extended narrow operand would compare 15 < 5
  // (false).
  EXPECT_EQ(val.value_or(-1), 1);
}

TEST(ConstEvalSteps, SignedEqualityConstantExpressionMutuallyDetermined) {
  // §11.8.2 exception 2: equality operands mutually determine the larger width
  // and sign-extend when signed. Both operands hold -1 at differing widths.
  EvalFixture f;
  auto* e = ParseExprFrom("-4'sd1 == -8'sd1", f);
  auto val = ConstEvalInt(e);
  ASSERT_TRUE(val.has_value());
  // Both are -1; zero-extending the narrow operand (15 vs 255) would differ.
  EXPECT_EQ(val.value_or(-1), 1);
}

}  // namespace
