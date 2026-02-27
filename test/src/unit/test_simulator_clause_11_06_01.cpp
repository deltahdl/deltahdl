// §11.6.1: Rules for expression bit lengths

#include <cstring>

#include "parser/ast.h"
#include "simulation/eval.h"

#include "fixture_simulator.h"
#include "builders_ast.h"

using namespace delta;

namespace {

// ==========================================================================
// Context-determined bit widths — §11.6.1
// ==========================================================================
TEST(EvalOpXZ, WidthPropFromContext) {
  SimFixture f;
  // 4-bit a + 4-bit b with 8-bit context → 8-bit result (no overflow).
  auto* va = f.ctx.CreateVariable("wa", 4);
  va->value = MakeLogic4VecVal(f.arena, 4, 0xF);
  auto* vb = f.ctx.CreateVariable("wb", 4);
  vb->value = MakeLogic4VecVal(f.arena, 4, 1);
  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "wa"),
                          MakeId(f.arena, "wb"));
  // Without context width: 4-bit result overflows to 0.
  auto r1 = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(r1.ToUint64(), 0u);
  // With context width 8: 8-bit result = 0x10.
  auto r2 = EvalExpr(expr, f.ctx, f.arena, 8);
  EXPECT_EQ(r2.ToUint64(), 0x10u);
  EXPECT_EQ(r2.width, 8u);
}

TEST(EvalOpXZ, TernaryWidthFromBranches) {
  SimFixture f;
  // ?: width = max(true_width, false_width)
  auto* cond = f.ctx.CreateVariable("tc", 1);
  cond->value = MakeLogic4VecVal(f.arena, 1, 1);
  auto* tv = f.ctx.CreateVariable("tv", 8);
  tv->value = MakeLogic4VecVal(f.arena, 8, 0xFF);
  auto* fv = f.ctx.CreateVariable("fv", 4);
  fv->value = MakeLogic4VecVal(f.arena, 4, 0xA);
  auto* tern = f.arena.Create<Expr>();
  tern->kind = ExprKind::kTernary;
  tern->condition = MakeId(f.arena, "tc");
  tern->true_expr = MakeId(f.arena, "tv");
  tern->false_expr = MakeId(f.arena, "fv");
  auto result = EvalExpr(tern, f.ctx, f.arena);
  // Width should be max(8,4) = 8, value 0xFF.
  EXPECT_EQ(result.width, 8u);
  EXPECT_EQ(result.ToUint64(), 0xFFu);
}

}  // namespace
