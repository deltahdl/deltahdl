#include "builders_ast.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(EvalSteps, ContextWidthPropagates) {
  SimFixture f;
  MakeVar(f, "a", 4, 0xF);
  MakeVar(f, "b", 4, 1);
  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "a"),
                          MakeId(f.arena, "b"));

  auto r1 = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(r1.ToUint64(), 0u);

  auto r2 = EvalExpr(expr, f.ctx, f.arena, 8);
  EXPECT_EQ(r2.ToUint64(), 0x10u);
}

TEST(EvalSteps, ShiftAmountSelfDetermined) {
  SimFixture f;
  MakeVar(f, "v", 8, 0x01);
  MakeVar(f, "sh", 4, 3);
  auto* expr = MakeBinary(f.arena, TokenKind::kLtLt, MakeId(f.arena, "v"),
                          MakeId(f.arena, "sh"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0x08u);
  EXPECT_EQ(result.width, 8u);
}

TEST(EvalSteps, SignedComparisonExtends) {
  SimFixture f;

  MakeSignedVarAdv(f, "s4", 4, 0xF);
  MakeSignedVarAdv(f, "s8", 8, 1);
  auto* expr = MakeBinary(f.arena, TokenKind::kLt, MakeId(f.arena, "s4"),
                          MakeId(f.arena, "s8"));
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalSteps, RelationalOperandsMutuallyDetermined) {
  SimFixture f;
  MakeVar(f, "r4", 4, 0xF);
  MakeVar(f, "r8", 8, 0x0F);
  auto* expr = MakeBinary(f.arena, TokenKind::kEqEq, MakeId(f.arena, "r4"),
                          MakeId(f.arena, "r8"));
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalSteps, TernaryCondSelfDetermined) {
  SimFixture f;
  MakeVar(f, "cond", 8, 0xFF);
  MakeVar(f, "tv", 8, 42);
  MakeVar(f, "fv", 4, 0);
  auto* tern = f.arena.Create<Expr>();
  tern->kind = ExprKind::kTernary;
  tern->condition = MakeId(f.arena, "cond");
  tern->true_expr = MakeId(f.arena, "tv");
  tern->false_expr = MakeId(f.arena, "fv");
  auto result = EvalExpr(tern, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

}  // namespace
