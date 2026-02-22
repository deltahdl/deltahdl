// §11.4.2: Increment and decrement operators

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"
#include <gtest/gtest.h>

using namespace delta;

// Shared fixture for expression evaluation tests.
struct EvalOpFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

// Helper: build an identifier Expr node.
static Expr *MakeId(Arena &arena, std::string_view name) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

// Helper: build a unary Expr.
static Expr *MakeUnary(Arena &arena, TokenKind op, Expr *operand) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kUnary;
  e->op = op;
  e->lhs = operand;
  return e;
}

namespace {

// ==========================================================================
// Postfix increment/decrement (i++, i--)
// ==========================================================================
// ==========================================================================
// Prefix increment/decrement (++i, --i)
// ==========================================================================
TEST(EvalOp, PrefixIncrement) {
  EvalOpFixture f;
  auto *var = f.ctx.CreateVariable("i", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 10);

  auto *pre = MakeUnary(f.arena, TokenKind::kPlusPlus, MakeId(f.arena, "i"));

  auto result = EvalExpr(pre, f.ctx, f.arena);
  // Returns NEW value (prefix semantics).
  EXPECT_EQ(result.ToUint64(), 11u);
  // Variable is now 11.
  EXPECT_EQ(var->value.ToUint64(), 11u);
}

TEST(EvalOp, PrefixDecrement) {
  EvalOpFixture f;
  auto *var = f.ctx.CreateVariable("j", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 5);

  auto *pre = MakeUnary(f.arena, TokenKind::kMinusMinus, MakeId(f.arena, "j"));

  auto result = EvalExpr(pre, f.ctx, f.arena);
  // Returns NEW value.
  EXPECT_EQ(result.ToUint64(), 4u);
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

TEST(EvalOp, PostfixIncrement) {
  EvalOpFixture f;
  auto *var = f.ctx.CreateVariable("i", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 10);

  auto *post = f.arena.Create<Expr>();
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
  EvalOpFixture f;
  auto *var = f.ctx.CreateVariable("j", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 5);

  auto *post = f.arena.Create<Expr>();
  post->kind = ExprKind::kPostfixUnary;
  post->op = TokenKind::kMinusMinus;
  post->lhs = MakeId(f.arena, "j");

  auto result = EvalExpr(post, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 5u);
  EXPECT_EQ(var->value.ToUint64(), 4u);
}

} // namespace
