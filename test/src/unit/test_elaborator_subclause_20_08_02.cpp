#include <gtest/gtest.h>

#include <cmath>
#include <limits>
#include <optional>

#include "elaborator/const_eval.h"
#include "fixture_evaluator.h"

using namespace delta;

namespace {

double FoldReal(const char* text, EvalFixture& f) {
  return ConstEvalReal(ParseExprFrom(text, f))
      .value_or(std::numeric_limits<double>::quiet_NaN());
}

TEST(ConstEvalRealMath, EachOneArgumentFunctionFolds) {
  EvalFixture f;
  EXPECT_DOUBLE_EQ(FoldReal("$ln(2.0)", f), std::log(2.0));
  EXPECT_DOUBLE_EQ(FoldReal("$log10(1000.0)", f), 3.0);
  EXPECT_DOUBLE_EQ(FoldReal("$exp(1.5)", f), std::exp(1.5));
  EXPECT_DOUBLE_EQ(FoldReal("$sqrt(2.25)", f), 1.5);
  EXPECT_DOUBLE_EQ(FoldReal("$floor(2.7)", f), 2.0);
  EXPECT_DOUBLE_EQ(FoldReal("$ceil(2.1)", f), 3.0);
  EXPECT_DOUBLE_EQ(FoldReal("$sin(0.5)", f), std::sin(0.5));
  EXPECT_DOUBLE_EQ(FoldReal("$cos(0.5)", f), std::cos(0.5));
  EXPECT_DOUBLE_EQ(FoldReal("$tan(0.5)", f), std::tan(0.5));
  EXPECT_DOUBLE_EQ(FoldReal("$asin(0.5)", f), std::asin(0.5));
  EXPECT_DOUBLE_EQ(FoldReal("$acos(0.5)", f), std::acos(0.5));
  EXPECT_DOUBLE_EQ(FoldReal("$atan(0.5)", f), std::atan(0.5));
  EXPECT_DOUBLE_EQ(FoldReal("$sinh(0.5)", f), std::sinh(0.5));
  EXPECT_DOUBLE_EQ(FoldReal("$cosh(0.5)", f), std::cosh(0.5));
  EXPECT_DOUBLE_EQ(FoldReal("$tanh(0.5)", f), std::tanh(0.5));
  EXPECT_DOUBLE_EQ(FoldReal("$asinh(0.5)", f), std::asinh(0.5));
  EXPECT_DOUBLE_EQ(FoldReal("$acosh(1.5)", f), std::acosh(1.5));
  EXPECT_DOUBLE_EQ(FoldReal("$atanh(0.5)", f), std::atanh(0.5));
}

TEST(ConstEvalRealMath, EachTwoArgumentFunctionFolds) {
  EvalFixture f;
  EXPECT_DOUBLE_EQ(FoldReal("$pow(3.0, 2.0)", f), 9.0);
  EXPECT_DOUBLE_EQ(FoldReal("$atan2(1.0, 2.0)", f), std::atan2(1.0, 2.0));
  EXPECT_DOUBLE_EQ(FoldReal("$hypot(3.0, 4.0)", f), 5.0);
}

TEST(ConstEvalRealMath, IntegerArgumentsAndNestingFold) {
  EvalFixture f;
  EXPECT_DOUBLE_EQ(FoldReal("$sqrt(16)", f), 4.0);
  EXPECT_DOUBLE_EQ(FoldReal("$pow(2, 5)", f), 32.0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$rtoi($pow(3, 2))", f)), 9);
}

TEST(ConstEvalRealMath, AnUnfoldableArgumentLeavesTheCallUnfolded) {
  EvalFixture f;
  EXPECT_FALSE(ConstEvalReal(ParseExprFrom("$sqrt(v)", f)).has_value());
  EXPECT_FALSE(ConstEvalReal(ParseExprFrom("$pow(2.0, v)", f)).has_value());
  EXPECT_FALSE(ConstEvalReal(ParseExprFrom("$sqrt()", f)).has_value());
}

}  // namespace
