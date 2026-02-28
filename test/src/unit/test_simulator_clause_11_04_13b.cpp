// §11.4.13: for an explanation of range list syntax.

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

// ==========================================================================
// Streaming concatenation ({<<{...}}, {>>{...}})
// ==========================================================================
TEST(EvalOp, StreamingLeftShift) {
  SimFixture f;
  // {<<{8'hAB}} — reverse bit order of 0xAB
  auto* var = f.ctx.CreateVariable("sv", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0xAB);

  auto* sc = f.arena.Create<Expr>();
  sc->kind = ExprKind::kStreamingConcat;
  sc->op = TokenKind::kLtLt;
  sc->elements.push_back(MakeId(f.arena, "sv"));

  auto result = EvalExpr(sc, f.ctx, f.arena);
  // 0xAB = 10101011 reversed = 11010101 = 0xD5
  EXPECT_EQ(result.ToUint64(), 0xD5u);
}

TEST(EvalOp, StreamingRightShift) {
  SimFixture f;
  // {>>{8'hAB}} — same order (no reversal)
  auto* var = f.ctx.CreateVariable("sv2", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0xAB);

  auto* sc = f.arena.Create<Expr>();
  sc->kind = ExprKind::kStreamingConcat;
  sc->op = TokenKind::kGtGt;
  sc->elements.push_back(MakeId(f.arena, "sv2"));

  auto result = EvalExpr(sc, f.ctx, f.arena);
  // Right-shift streaming: no bit reversal, just concatenate in order.
  EXPECT_EQ(result.ToUint64(), 0xABu);
}

}  // namespace
