#include "builders_ast.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

inline Expr* MakeTernary(Arena& arena, Expr* cond, Expr* t, Expr* f) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kTernary;
  e->condition = cond;
  e->true_expr = t;
  e->false_expr = f;
  return e;
}

TEST(ShortCircuit, LogicalAndShortCircuitsOnFalseLhs) {
  SimFixture f;
  MakeVar(f, "a", 8, 0);
  MakeVar(f, "b", 8, 42);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kAmpAmp,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(ShortCircuit, LogicalAndEvaluatesRhsWhenLhsTrue) {
  SimFixture f;
  MakeVar(f, "a", 8, 1);
  MakeVar(f, "b", 8, 1);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kAmpAmp,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(ShortCircuit, LogicalOrShortCircuitsOnTrueLhs) {
  SimFixture f;
  MakeVar(f, "a", 8, 5);
  MakeVar(f, "b", 8, 0);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kPipePipe,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(ShortCircuit, LogicalOrEvaluatesRhsWhenLhsFalse) {
  SimFixture f;
  MakeVar(f, "a", 8, 0);
  MakeVar(f, "b", 8, 0);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kPipePipe,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(ShortCircuit, ImplicationShortCircuitsOnFalseLhs) {
  SimFixture f;
  MakeVar(f, "a", 8, 0);
  MakeVar(f, "b", 8, 99);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kArrow,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(ShortCircuit, TernaryEvaluatesTrueBranchOnly) {
  SimFixture f;
  MakeVar(f, "c", 8, 1);
  MakeVar(f, "t", 8, 10);
  MakeVar(f, "e", 8, 20);
  auto result =
      EvalExpr(MakeTernary(f.arena, MakeId(f.arena, "c"), MakeId(f.arena, "t"),
                           MakeId(f.arena, "e")),
               f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 10u);
}

TEST(ShortCircuit, TernaryEvaluatesFalseBranchOnly) {
  SimFixture f;
  MakeVar(f, "c", 8, 0);
  MakeVar(f, "t", 8, 10);
  MakeVar(f, "e", 8, 20);
  auto result =
      EvalExpr(MakeTernary(f.arena, MakeId(f.arena, "c"), MakeId(f.arena, "t"),
                           MakeId(f.arena, "e")),
               f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 20u);
}

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
