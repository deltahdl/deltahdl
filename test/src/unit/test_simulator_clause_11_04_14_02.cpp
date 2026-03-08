#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(EvalOp, StreamingLeftShift) {
  SimFixture f;

  auto* var = f.ctx.CreateVariable("sv", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0xAB);

  auto* sc = f.arena.Create<Expr>();
  sc->kind = ExprKind::kStreamingConcat;
  sc->op = TokenKind::kLtLt;
  sc->elements.push_back(MakeId(f.arena, "sv"));

  auto result = EvalExpr(sc, f.ctx, f.arena);

  EXPECT_EQ(result.ToUint64(), 0xD5u);
}

TEST(EvalOp, StreamingRightShift) {
  SimFixture f;

  auto* var = f.ctx.CreateVariable("sv2", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0xAB);

  auto* sc = f.arena.Create<Expr>();
  sc->kind = ExprKind::kStreamingConcat;
  sc->op = TokenKind::kGtGt;
  sc->elements.push_back(MakeId(f.arena, "sv2"));

  auto result = EvalExpr(sc, f.ctx, f.arena);

  EXPECT_EQ(result.ToUint64(), 0xABu);
}

}
