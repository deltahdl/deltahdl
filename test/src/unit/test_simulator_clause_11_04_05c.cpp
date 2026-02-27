// §11.4.5: Equality operators


#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/eval_array.h"

#include "fixture_simulator.h"
#include "helpers_array.h"

using namespace delta;

// =============================================================================
// Helper fixture
// =============================================================================
static Expr* MkEq(Arena& arena, std::string_view a, std::string_view b) {
  auto* expr = arena.Create<Expr>();
  expr->kind = ExprKind::kBinary;
  expr->op = TokenKind::kEqEq;
  auto* lhs = arena.Create<Expr>();
  lhs->kind = ExprKind::kIdentifier;
  lhs->text = a;
  auto* rhs = arena.Create<Expr>();
  rhs->kind = ExprKind::kIdentifier;
  rhs->text = b;
  expr->lhs = lhs;
  expr->rhs = rhs;
  return expr;
}

namespace {

TEST(ArrayEquality, EqualArrays) {
  SimFixture f;
  MakeArray4(f, "a");
  MakeArray4(f, "b");
  auto result = EvalExpr(MkEq(f.arena, "a", "b"), f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(ArrayEquality, UnequalArrays) {
  SimFixture f;
  MakeArray4(f, "a");
  MakeArray4(f, "b");
  // Modify b[2] to differ.
  auto* v = f.ctx.FindVariable("b[2]");
  ASSERT_NE(v, nullptr);
  v->value = MakeLogic4VecVal(f.arena, 8, 99);
  auto result = EvalExpr(MkEq(f.arena, "a", "b"), f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
