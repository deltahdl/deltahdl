// §11.11: Minimum, typical, and maximum delay expressions

#include <cstring>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

// ==========================================================================
// MinTypMax evaluation — §11.11
// ==========================================================================
TEST(EvalOpXZ, MinTypMaxDefaultTyp) {
  SimFixture f;
  // Default delay mode is typ — should return middle expression.
  auto* mtm = f.arena.Create<Expr>();
  mtm->kind = ExprKind::kMinTypMax;
  mtm->lhs = MakeInt(f.arena, 10);        // min
  mtm->condition = MakeInt(f.arena, 20);  // typ
  mtm->rhs = MakeInt(f.arena, 30);        // max
  auto result = EvalExpr(mtm, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 20u);
}

TEST(EvalOpXZ, MinTypMaxMin) {
  SimFixture f;
  f.ctx.SetDelayMode(DelayMode::kMin);
  auto* mtm = f.arena.Create<Expr>();
  mtm->kind = ExprKind::kMinTypMax;
  mtm->lhs = MakeInt(f.arena, 10);
  mtm->condition = MakeInt(f.arena, 20);
  mtm->rhs = MakeInt(f.arena, 30);
  auto result = EvalExpr(mtm, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 10u);
}

TEST(EvalOpXZ, MinTypMaxMax) {
  SimFixture f;
  f.ctx.SetDelayMode(DelayMode::kMax);
  auto* mtm = f.arena.Create<Expr>();
  mtm->kind = ExprKind::kMinTypMax;
  mtm->lhs = MakeInt(f.arena, 10);
  mtm->condition = MakeInt(f.arena, 20);
  mtm->rhs = MakeInt(f.arena, 30);
  auto result = EvalExpr(mtm, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 30u);
}

}  // namespace
