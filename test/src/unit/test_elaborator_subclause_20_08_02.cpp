#include <gtest/gtest.h>

#include <cmath>
#include <limits>
#include <optional>

#include "elaborator/const_eval.h"
#include "fixture_evaluator.h"

using namespace delta;

namespace {

// The constant real value of `text`, NaN where it does not fold, which no
// expectation below equals.
double FoldReal(const char* text, EvalFixture& f) {
  return ConstEvalReal(ParseExprFrom(text, f))
      .value_or(std::numeric_limits<double>::quiet_NaN());
}

// §20.8.2, Table 20-4: each real math function of one argument folds in a
// constant expression to the C function it corresponds to.
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

// §20.8.2, Table 20-4: the functions of two arguments fold the same way.
TEST(ConstEvalRealMath, EachTwoArgumentFunctionFolds) {
  EvalFixture f;
  EXPECT_DOUBLE_EQ(FoldReal("$pow(3.0, 2.0)", f), 9.0);
  EXPECT_DOUBLE_EQ(FoldReal("$atan2(1.0, 2.0)", f), std::atan2(1.0, 2.0));
  EXPECT_DOUBLE_EQ(FoldReal("$hypot(3.0, 4.0)", f), 5.0);
}

// §20.8.2: an integer argument is converted to real, and a real math function
// nested in $rtoi folds to an integer constant.
TEST(ConstEvalRealMath, IntegerArgumentsAndNestingFold) {
  EvalFixture f;
  EXPECT_DOUBLE_EQ(FoldReal("$sqrt(16)", f), 4.0);
  EXPECT_DOUBLE_EQ(FoldReal("$pow(2, 5)", f), 32.0);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$rtoi($pow(3, 2))", f)), 9);
}

// §20.8.2: a call with an argument that does not fold, or with no argument,
// does not fold either.
TEST(ConstEvalRealMath, AnUnfoldableArgumentLeavesTheCallUnfolded) {
  EvalFixture f;
  EXPECT_FALSE(ConstEvalReal(ParseExprFrom("$sqrt(v)", f)).has_value());
  EXPECT_FALSE(ConstEvalReal(ParseExprFrom("$pow(2.0, v)", f)).has_value());
  EXPECT_FALSE(ConstEvalReal(ParseExprFrom("$sqrt()", f)).has_value());
}

}  // namespace
