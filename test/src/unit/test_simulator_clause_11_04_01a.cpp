// Non-LRM tests

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

TEST(EvalOp, StarEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 6);

  auto* expr = MakeBinary(f.arena, TokenKind::kStarEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 7));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(EvalOp, SlashEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 100);

  auto* expr = MakeBinary(f.arena, TokenKind::kSlashEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 20u);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(EvalOp, PercentEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("m", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 17);

  auto* expr = MakeBinary(f.arena, TokenKind::kPercentEq, MakeId(f.arena, "m"),
                          MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 2u);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

}  // namespace
