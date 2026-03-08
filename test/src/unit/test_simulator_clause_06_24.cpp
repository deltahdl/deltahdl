#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(EvalOp, CastTruncate) {
  SimFixture f;

  auto* cast = f.arena.Create<Expr>();
  cast->kind = ExprKind::kCast;
  cast->text = "byte";
  cast->lhs = MakeInt(f.arena, 0x1FF);

  auto result = EvalExpr(cast, f.ctx, f.arena);

  EXPECT_EQ(result.ToUint64(), 0xFFu);
  EXPECT_EQ(result.width, 8u);
}

TEST(EvalOp, CastWiden) {
  SimFixture f;

  auto* cast = f.arena.Create<Expr>();
  cast->kind = ExprKind::kCast;
  cast->text = "int";
  cast->lhs = MakeInt(f.arena, 42);

  auto result = EvalExpr(cast, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
  EXPECT_EQ(result.width, 32u);
}

TEST(EvalOp, CastShortint) {
  SimFixture f;
  auto* cast = f.arena.Create<Expr>();
  cast->kind = ExprKind::kCast;
  cast->text = "shortint";
  cast->lhs = MakeInt(f.arena, 0x1ABCD);

  auto result = EvalExpr(cast, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xABCDu);
  EXPECT_EQ(result.width, 16u);
}

}
