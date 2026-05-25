#include "fixture_evaluator.h"

using namespace delta;

namespace {

// §20.7 states that an array query function call is legal within a constant
// expression when the type of its first argument is a fixed-size type, even
// though the data object named by that argument is not itself a constant. The
// elaborator must therefore treat such a call as constant even when its
// operand is not a constant operand. Each query function is exercised with a
// non-constant (undeclared, hence out-of-scope) array operand.

TEST(ArrayQueryConstExpr, SizeWithNonConstArgIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("$size(arr)", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

TEST(ArrayQueryConstExpr, DimensionsWithNonConstArgIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("$dimensions(arr)", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

TEST(ArrayQueryConstExpr, UnpackedDimensionsWithNonConstArgIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("$unpacked_dimensions(arr)", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

TEST(ArrayQueryConstExpr, LeftWithNonConstArgIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("$left(arr)", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

TEST(ArrayQueryConstExpr, RightWithNonConstArgIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("$right(arr)", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

TEST(ArrayQueryConstExpr, LowWithNonConstArgIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("$low(arr)", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

TEST(ArrayQueryConstExpr, HighWithNonConstArgIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("$high(arr)", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

TEST(ArrayQueryConstExpr, IncrementWithNonConstArgIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("$increment(arr)", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

// A query with an explicit constant dimension expression is also constant.
TEST(ArrayQueryConstExpr, SizeWithDimensionExprIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("$size(arr, 2)", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

}
