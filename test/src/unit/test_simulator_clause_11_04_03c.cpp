// §11.4.3: Arithmetic operators


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
// Power operator (**)
// ==========================================================================
TEST(EvalOp, PowerBasic) {
  SimFixture f;
  // 2 ** 10 = 1024
  auto* expr = MakeBinary(f.arena, TokenKind::kPower, MakeInt(f.arena, 2),
                          MakeInt(f.arena, 10));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1024u);
}

TEST(EvalOp, PowerZeroExponent) {
  SimFixture f;
  // 5 ** 0 = 1
  auto* expr = MakeBinary(f.arena, TokenKind::kPower, MakeInt(f.arena, 5),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, PowerOneExponent) {
  SimFixture f;
  // 7 ** 1 = 7
  auto* expr = MakeBinary(f.arena, TokenKind::kPower, MakeInt(f.arena, 7),
                          MakeInt(f.arena, 1));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 7u);
}

}  // namespace
