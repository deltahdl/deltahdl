// Non-LRM tests

#include "fixture_elaborator.h"
#include "fixture_evaluator.h"

using namespace delta;

namespace {

// §11.2.1: Constant system function call — $clog2 with non-constant arg
// is not constant.
TEST(ConstExpr, Clog2NonConstantArgNotConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("$clog2(x)", f);
  EXPECT_FALSE(IsConstantExpr(e));
}

// §11.2.1: $bits is a constant system function even with type argument.
TEST(ConstExpr, BitsIsConstantSysFunc) {
  EvalFixture f;
  auto* e = ParseExprFrom("$bits(32'd0)", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

// §11.2.1: $countones with constant arg is constant.
TEST(ConstExpr, CountonesConstantArg) {
  EvalFixture f;
  auto* e = ParseExprFrom("$countones(8'hFF)", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

// §11.2.1: $onehot with constant arg is constant.
TEST(ConstExpr, OnehotConstantArg) {
  EvalFixture f;
  auto* e = ParseExprFrom("$onehot(8'h04)", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

// §11.2.1: $onehot0 with constant arg is constant.
TEST(ConstExpr, Onehot0ConstantArg) {
  EvalFixture f;
  auto* e = ParseExprFrom("$onehot0(8'h00)", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

// §11.2.1: ConstEvalReal — real literal evaluates to double.
TEST(ConstEvalReal, RealLiteralEval) {
  EvalFixture f;
  auto* e = ParseExprFrom("3.14", f);
  auto val = ConstEvalReal(e);
  ASSERT_TRUE(val.has_value());
  EXPECT_NEAR(*val, 3.14, 1e-6);
}

// §11.2.1: ConstEvalReal — integer literal promotes to real.
TEST(ConstEvalReal, IntLiteralPromotesToReal) {
  EvalFixture f;
  auto* e = ParseExprFrom("42", f);
  auto val = ConstEvalReal(e);
  ASSERT_TRUE(val.has_value());
  EXPECT_DOUBLE_EQ(*val, 42.0);
}

// §11.2.1: ConstEvalReal — unary minus on real.
TEST(ConstEvalReal, UnaryMinusOnReal) {
  EvalFixture f;
  auto* e = ParseExprFrom("-3.14", f);
  auto val = ConstEvalReal(e);
  ASSERT_TRUE(val.has_value());
  EXPECT_NEAR(*val, -3.14, 1e-6);
}

// §11.2.1: ConstEvalReal — binary add on reals.
TEST(ConstEvalReal, BinaryAddReals) {
  EvalFixture f;
  auto* e = ParseExprFrom("1.5 + 2.5", f);
  auto val = ConstEvalReal(e);
  ASSERT_TRUE(val.has_value());
  EXPECT_DOUBLE_EQ(*val, 4.0);
}

// §11.2.1: ConstEvalReal — binary multiply on reals.
TEST(ConstEvalReal, BinaryMulReals) {
  EvalFixture f;
  auto* e = ParseExprFrom("2.0 * 3.0", f);
  auto val = ConstEvalReal(e);
  ASSERT_TRUE(val.has_value());
  EXPECT_DOUBLE_EQ(*val, 6.0);
}

// §11.2.1: ConstEvalReal — division by zero returns nullopt.
TEST(ConstEvalReal, DivByZeroReturnsNullopt) {
  EvalFixture f;
  auto* e = ParseExprFrom("1.0 / 0.0", f);
  auto val = ConstEvalReal(e);
  EXPECT_FALSE(val.has_value());
}

// §11.2.1: ConstEvalReal — ternary on reals.
TEST(ConstEvalReal, TernaryOnReals) {
  EvalFixture f;
  auto* e = ParseExprFrom("1 ? 2.5 : 3.5", f);
  auto val = ConstEvalReal(e);
  ASSERT_TRUE(val.has_value());
  EXPECT_DOUBLE_EQ(*val, 2.5);
}

// §11.2.1: ConstEvalReal — non-constant returns nullopt.
TEST(ConstEvalReal, NonConstantReturnsNullopt) {
  EvalFixture f;
  auto* e = ParseExprFrom("x", f);
  auto val = ConstEvalReal(e);
  EXPECT_FALSE(val.has_value());
}

// §11.2.1: Elaborator rejects non-constant in parameter default.
TEST(ConstExprElab, NonConstantParamDefaultWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int P = x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  // Non-constant param default: param not resolved.
  EXPECT_FALSE(design->top_modules[0]->params[0].is_resolved);
}

// §11.2.1: Constant expressions can use any operator from Table 11-1.
TEST(ConstExpr, PowerOperatorInConstantExpr) {
  EvalFixture f;
  ScopeMap scope;
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("2 ** 10", f), scope), 1024);
}

// §11.2.1: Constant expression with nested ternary.
TEST(ConstExpr, NestedTernaryIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("1 ? (0 ? 3 : 4) : 5", f);
  EXPECT_TRUE(IsConstantExpr(e));
  EXPECT_EQ(ConstEvalInt(e), 4);
}

// §11.2.1: Unbased unsized literal is a constant expression.
TEST(ConstExpr, UnbasedUnsizedLiteralIsConstant) {
  EvalFixture f;
  auto* e = ParseExprFrom("'1", f);
  EXPECT_TRUE(IsConstantExpr(e));
}

}  // namespace
