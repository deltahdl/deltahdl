// §20.8: Math functions

#include <gtest/gtest.h>

#include <cmath>

#include "fixture_real.h"
#include "parser/ast.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

// =============================================================================
// §20.8: Math system calls with real args
// =============================================================================
TEST(RealTypes, MathSqrtReal) {
  RealFixture f;
  // $sqrt(4.0) should return 2.0.
  auto* call = f.arena.Create<Expr>();
  call->kind = ExprKind::kSystemCall;
  call->callee = "$sqrt";
  call->args = {f.MakeRealLiteral(4.0)};
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_NEAR(VecToDouble(result), 2.0, 1e-10);
}

TEST(RealTypes, MathLnReal) {
  RealFixture f;
  // $ln(1.0) should return 0.0.
  auto* call = f.arena.Create<Expr>();
  call->kind = ExprKind::kSystemCall;
  call->callee = "$ln";
  call->args = {f.MakeRealLiteral(1.0)};
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_NEAR(VecToDouble(result), 0.0, 1e-10);
}

}  // namespace
