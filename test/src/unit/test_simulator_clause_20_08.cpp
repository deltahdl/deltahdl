#include <gtest/gtest.h>

#include <cmath>

#include "fixture_real.h"
#include "helpers_eval_op.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(RealTypes, MathSqrtReal) {
  RealFixture f;

  auto* call = f.arena.Create<Expr>();
  call->kind = ExprKind::kSystemCall;
  call->callee = "$sqrt";
  call->args = {f.MakeRealLiteral(4.0)};
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_NEAR(VecToDouble(result), 2.0, 1e-10);
}

TEST(RealTypes, MathLnReal) {
  RealFixture f;

  auto* call = f.arena.Create<Expr>();
  call->kind = ExprKind::kSystemCall;
  call->callee = "$ln";
  call->args = {f.MakeRealLiteral(1.0)};
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_NEAR(VecToDouble(result), 0.0, 1e-10);
}

}  // namespace
