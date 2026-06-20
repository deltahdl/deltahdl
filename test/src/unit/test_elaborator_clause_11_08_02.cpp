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

}  // namespace
