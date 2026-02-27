// §6.24: Casting


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

namespace {

// ==========================================================================
// Cast (type'(expr))
// ==========================================================================
TEST(EvalOp, CastTruncate) {
  SimFixture f;
  // Cast a 32-bit value to a narrower type (truncate).
  // We test by evaluating the inner expression and checking the result.
  auto* cast = f.arena.Create<Expr>();
  cast->kind = ExprKind::kCast;
  cast->text = "byte";                  // 8-bit type
  cast->lhs = MakeInt(f.arena, 0x1FF);  // 511

  auto result = EvalExpr(cast, f.ctx, f.arena);
  // byte is 8-bit: 0x1FF & 0xFF = 0xFF = 255
  EXPECT_EQ(result.ToUint64(), 0xFFu);
  EXPECT_EQ(result.width, 8u);
}

TEST(EvalOp, CastWiden) {
  SimFixture f;
  // Cast to int (32-bit) — value should be preserved.
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
  cast->text = "shortint";  // 16-bit type
  cast->lhs = MakeInt(f.arena, 0x1ABCD);

  auto result = EvalExpr(cast, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0xABCDu);
  EXPECT_EQ(result.width, 16u);
}

}  // namespace
