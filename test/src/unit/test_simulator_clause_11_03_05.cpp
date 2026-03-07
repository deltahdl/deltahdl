#include "builders_ast.h"
#include "fixture_simulator.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

// Helper: build a ternary (condition ? true_expr : false_expr).
inline Expr* MakeTernary(Arena& arena, Expr* cond, Expr* t, Expr* f) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kTernary;
  e->condition = cond;
  e->true_expr = t;
  e->false_expr = f;
  return e;
}

// §11.3.5: Logical AND short-circuits when LHS is 0.
// When a == 0, b is not needed to determine result is 0.
TEST(ShortCircuit, LogicalAndShortCircuitsOnFalseLhs) {
  SimFixture f;
  MakeVar(f, "a", 8, 0);
  MakeVar(f, "b", 8, 42);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kAmpAmp,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// §11.3.5: Logical AND evaluates RHS when LHS is nonzero.
TEST(ShortCircuit, LogicalAndEvaluatesRhsWhenLhsTrue) {
  SimFixture f;
  MakeVar(f, "a", 8, 1);
  MakeVar(f, "b", 8, 1);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kAmpAmp,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// §11.3.5: Logical OR short-circuits when LHS is nonzero.
TEST(ShortCircuit, LogicalOrShortCircuitsOnTrueLhs) {
  SimFixture f;
  MakeVar(f, "a", 8, 5);
  MakeVar(f, "b", 8, 0);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kPipePipe,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// §11.3.5: Logical OR evaluates RHS when LHS is 0.
TEST(ShortCircuit, LogicalOrEvaluatesRhsWhenLhsFalse) {
  SimFixture f;
  MakeVar(f, "a", 8, 0);
  MakeVar(f, "b", 8, 0);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kPipePipe,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// §11.3.5: Implication short-circuits when LHS is false.
// false -> anything = true, without evaluating RHS.
TEST(ShortCircuit, ImplicationShortCircuitsOnFalseLhs) {
  SimFixture f;
  MakeVar(f, "a", 8, 0);
  MakeVar(f, "b", 8, 99);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kArrow,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

// §11.3.5: Ternary evaluates only the true branch when condition is true.
TEST(ShortCircuit, TernaryEvaluatesTrueBranchOnly) {
  SimFixture f;
  MakeVar(f, "c", 8, 1);
  MakeVar(f, "t", 8, 10);
  MakeVar(f, "e", 8, 20);
  auto result = EvalExpr(MakeTernary(f.arena, MakeId(f.arena, "c"),
                                     MakeId(f.arena, "t"), MakeId(f.arena, "e")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 10u);
}

// §11.3.5: Ternary evaluates only the false branch when condition is false.
TEST(ShortCircuit, TernaryEvaluatesFalseBranchOnly) {
  SimFixture f;
  MakeVar(f, "c", 8, 0);
  MakeVar(f, "t", 8, 10);
  MakeVar(f, "e", 8, 20);
  auto result = EvalExpr(MakeTernary(f.arena, MakeId(f.arena, "c"),
                                     MakeId(f.arena, "t"), MakeId(f.arena, "e")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 20u);
}

// §11.3.5: Bitwise AND does NOT short-circuit — both operands always evaluated.
TEST(ShortCircuit, BitwiseAndAlwaysEvaluatesBothOperands) {
  SimFixture f;
  MakeVar(f, "a", 8, 0);
  MakeVar(f, "b", 8, 0xFF);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kAmp,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
