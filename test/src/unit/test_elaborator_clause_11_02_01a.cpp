// Non-LRM tests

#include "fixture_elaborator.h"
#include "fixture_evaluator.h"

using namespace delta;

namespace {

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
