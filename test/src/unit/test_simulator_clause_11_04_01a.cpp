// §11.4.1: Assignment operators


#include "lexer/token.h"
#include "parser/ast.h"
#include "simulation/eval.h"

#include "fixture_simulator.h"

using namespace delta;

// Shared fixture for expression evaluation tests.
// Helper: build a simple integer literal Expr node.
static Expr* MakeInt(Arena& arena, uint64_t val) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

// Helper: build an identifier Expr node.
static Expr* MakeId(Arena& arena, std::string_view name) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

// Helper: build a binary Expr.
static Expr* MakeBinary(Arena& arena, TokenKind op, Expr* lhs, Expr* rhs) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kBinary;
  e->op = op;
  e->lhs = lhs;
  e->rhs = rhs;
  return e;
}

namespace {

// ==========================================================================
// Compound assignment operators (+=, -=, *=, /=, %=, &=, |=, ^=, <<=, >>=)
// ==========================================================================
TEST(EvalOp, PlusEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 10);

  auto* expr = MakeBinary(f.arena, TokenKind::kPlusEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 5));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 15u);
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

TEST(EvalOp, MinusEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 20);

  auto* expr = MakeBinary(f.arena, TokenKind::kMinusEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 7));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 13u);
  EXPECT_EQ(var->value.ToUint64(), 13u);
}

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
