#include <cstring>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_mintymax.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(MinTypMaxEval, DefaultTyp) {
  SimFixture f;

  auto* mtm = f.arena.Create<Expr>();
  mtm->kind = ExprKind::kMinTypMax;
  mtm->lhs = MakeInt(f.arena, 10);
  mtm->condition = MakeInt(f.arena, 20);
  mtm->rhs = MakeInt(f.arena, 30);
  auto result = EvalExpr(mtm, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 20u);
}

TEST(MinTypMaxEval, SelectsMin) {
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

TEST(MinTypMaxEval, SelectsMax) {
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
TEST(MinTypMaxEval, SubExpressionsAddedPerMode) {
  SimFixture f;
  // LRM Example 1: (a:b:c) + (d:e:f) => min=a+d, typ=b+e, max=c+f
  auto* lhs_mtm = f.arena.Create<Expr>();
  lhs_mtm->kind = ExprKind::kMinTypMax;
  lhs_mtm->lhs = MakeInt(f.arena, 1);
  lhs_mtm->condition = MakeInt(f.arena, 2);
  lhs_mtm->rhs = MakeInt(f.arena, 3);

  auto* rhs_mtm = f.arena.Create<Expr>();
  rhs_mtm->kind = ExprKind::kMinTypMax;
  rhs_mtm->lhs = MakeInt(f.arena, 10);
  rhs_mtm->condition = MakeInt(f.arena, 20);
  rhs_mtm->rhs = MakeInt(f.arena, 30);

  auto* add = MakeBinary(f.arena, TokenKind::kPlus, lhs_mtm, rhs_mtm);

  f.ctx.SetDelayMode(DelayMode::kMin);
  EXPECT_EQ(EvalExpr(add, f.ctx, f.arena).ToUint64(), 11u);

  f.ctx.SetDelayMode(DelayMode::kTyp);
  EXPECT_EQ(EvalExpr(add, f.ctx, f.arena).ToUint64(), 22u);

  f.ctx.SetDelayMode(DelayMode::kMax);
  EXPECT_EQ(EvalExpr(add, f.ctx, f.arena).ToUint64(), 33u);
}

TEST(MinTypMaxEval, SingleExpressionFallthrough) {
  SimFixture f;
  auto* expr = MakeInt(f.arena, 42);
  f.ctx.SetDelayMode(DelayMode::kMin);
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 42u);
  f.ctx.SetDelayMode(DelayMode::kMax);
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 42u);
}

TEST(MinTypMaxEval, AllThreeValuesSame) {
  SimFixture f;
  auto* mtm = f.arena.Create<Expr>();
  mtm->kind = ExprKind::kMinTypMax;
  mtm->lhs = MakeInt(f.arena, 7);
  mtm->condition = MakeInt(f.arena, 7);
  mtm->rhs = MakeInt(f.arena, 7);

  f.ctx.SetDelayMode(DelayMode::kMin);
  EXPECT_EQ(EvalExpr(mtm, f.ctx, f.arena).ToUint64(), 7u);
  f.ctx.SetDelayMode(DelayMode::kTyp);
  EXPECT_EQ(EvalExpr(mtm, f.ctx, f.arena).ToUint64(), 7u);
  f.ctx.SetDelayMode(DelayMode::kMax);
  EXPECT_EQ(EvalExpr(mtm, f.ctx, f.arena).ToUint64(), 7u);
}

}  // namespace
