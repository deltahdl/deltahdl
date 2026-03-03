// Non-LRM tests

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

TEST(EvalOp, PostfixIncrement) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("i", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 10);

  auto* post = f.arena.Create<Expr>();
  post->kind = ExprKind::kPostfixUnary;
  post->op = TokenKind::kPlusPlus;
  post->lhs = MakeId(f.arena, "i");

  auto result = EvalExpr(post, f.ctx, f.arena);
  // Returns original value.
  EXPECT_EQ(result.ToUint64(), 10u);
  // Variable is now 11.
  EXPECT_EQ(var->value.ToUint64(), 11u);
}

TEST(EvalOp, PostfixDecrement) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("j", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 5);

  auto* post = f.arena.Create<Expr>();
  post->kind = ExprKind::kPostfixUnary;
  post->op = TokenKind::kMinusMinus;
  post->lhs = MakeId(f.arena, "j");

  auto result = EvalExpr(post, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 5u);
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

}  // namespace
