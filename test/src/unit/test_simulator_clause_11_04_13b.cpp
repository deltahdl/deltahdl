// §11.4.13: for an explanation of range list syntax.

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"
#include <gtest/gtest.h>

using namespace delta;

// Shared fixture for expression evaluation tests.
struct EvalOpFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

// Helper: build an identifier Expr node.
static Expr *MakeId(Arena &arena, std::string_view name) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

namespace {

// ==========================================================================
// Streaming concatenation ({<<{...}}, {>>{...}})
// ==========================================================================
TEST(EvalOp, StreamingLeftShift) {
  EvalOpFixture f;
  // {<<{8'hAB}} — reverse bit order of 0xAB
  auto *var = f.ctx.CreateVariable("sv", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0xAB);

  auto *sc = f.arena.Create<Expr>();
  sc->kind = ExprKind::kStreamingConcat;
  sc->op = TokenKind::kLtLt;
  sc->elements.push_back(MakeId(f.arena, "sv"));

  auto result = EvalExpr(sc, f.ctx, f.arena);
  // 0xAB = 10101011 reversed = 11010101 = 0xD5
  EXPECT_EQ(result.ToUint64(), 0xD5u);
}

TEST(EvalOp, StreamingRightShift) {
  EvalOpFixture f;
  // {>>{8'hAB}} — same order (no reversal)
  auto *var = f.ctx.CreateVariable("sv2", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0xAB);

  auto *sc = f.arena.Create<Expr>();
  sc->kind = ExprKind::kStreamingConcat;
  sc->op = TokenKind::kGtGt;
  sc->elements.push_back(MakeId(f.arena, "sv2"));

  auto result = EvalExpr(sc, f.ctx, f.arena);
  // Right-shift streaming: no bit reversal, just concatenate in order.
  EXPECT_EQ(result.ToUint64(), 0xABu);
}

} // namespace
