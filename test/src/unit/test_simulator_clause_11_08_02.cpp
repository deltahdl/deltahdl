#include "builders_ast.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// §11.8.2: Context width propagates to operands of arithmetic expressions.
TEST(EvalSteps, ContextWidthPropagates) {
  SimFixture f;
  MakeVar(f, "a", 4, 0xF);
  MakeVar(f, "b", 4, 1);
  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "a"),
                          MakeId(f.arena, "b"));
  // Without context: 4-bit, wraps to 0.
  auto r1 = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(r1.ToUint64(), 0u);
  // With 8-bit context: carries into bit 4.
  auto r2 = EvalExpr(expr, f.ctx, f.arena, 8);
  EXPECT_EQ(r2.ToUint64(), 0x10u);
}

// §11.8.2: Self-determined operands are not affected by context.
// The shift amount (RHS of shift) is self-determined.
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

// §11.8.2: Signed comparison — both signed, sign-extended to max width.
TEST(EvalSteps, SignedComparisonExtends) {
  SimFixture f;
  // -1 in 4 bits = 0xF, sign-extended to 8 bits = 0xFF = -1
  MakeSignedVarAdv(f, "s4", 4, 0xF);
  MakeSignedVarAdv(f, "s8", 8, 1);
  auto* expr = MakeBinary(f.arena, TokenKind::kLt, MakeId(f.arena, "s4"),
                          MakeId(f.arena, "s8"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  // -1 < 1 → true
  EXPECT_EQ(result.ToUint64(), 1u);
}

// §11.8.2: Relational/equality operands are context-determined to each other.
TEST(EvalSteps, RelationalOperandsMutuallyDetermined) {
  SimFixture f;
  MakeVar(f, "r4", 4, 0xF);
  MakeVar(f, "r8", 8, 0x0F);
  auto* expr = MakeBinary(f.arena, TokenKind::kEqEq, MakeId(f.arena, "r4"),
                          MakeId(f.arena, "r8"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  // 4'hF zero-extended to 8 bits = 8'h0F, equals 8'h0F → 1.
  EXPECT_EQ(result.ToUint64(), 1u);
}

// §11.8.2: Ternary condition is self-determined; branches are
// context-determined.
TEST(EvalSteps, TernaryCondSelfDetermined) {
  SimFixture f;
  MakeVar(f, "cond", 8, 0xFF);  // Nonzero → true.
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
