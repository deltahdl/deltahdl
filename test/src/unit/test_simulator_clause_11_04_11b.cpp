// §11.4.11: Conditional operator

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

using namespace delta;

// Shared fixture for expression evaluation tests.
struct EvalOpFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

// Helper: build a simple integer literal Expr node.
static Expr *MakeInt(Arena &arena, uint64_t val) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

namespace {

// ==========================================================================
// Inside operator (expr inside {val1, val2, [lo:hi]})
// ==========================================================================
TEST(EvalOp, InsideMatch) {
  EvalOpFixture f;
  // 5 inside {3, 5, 7} = 1
  auto *inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeInt(f.arena, 5);
  inside->elements.push_back(MakeInt(f.arena, 3));
  inside->elements.push_back(MakeInt(f.arena, 5));
  inside->elements.push_back(MakeInt(f.arena, 7));

  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, InsideNoMatch) {
  EvalOpFixture f;
  // 4 inside {3, 5, 7} = 0
  auto *inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeInt(f.arena, 4);
  inside->elements.push_back(MakeInt(f.arena, 3));
  inside->elements.push_back(MakeInt(f.arena, 5));
  inside->elements.push_back(MakeInt(f.arena, 7));

  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(EvalOp, InsideRange) {
  EvalOpFixture f;
  // 5 inside {[3:7]} = 1 (range element)
  auto *range = f.arena.Create<Expr>();
  range->kind = ExprKind::kSelect;
  range->index = MakeInt(f.arena, 3);
  range->index_end = MakeInt(f.arena, 7);

  auto *inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeInt(f.arena, 5);
  inside->elements.push_back(range);

  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalOp, InsideRangeNoMatch) {
  EvalOpFixture f;
  // 10 inside {[3:7]} = 0
  auto *range = f.arena.Create<Expr>();
  range->kind = ExprKind::kSelect;
  range->index = MakeInt(f.arena, 3);
  range->index_end = MakeInt(f.arena, 7);

  auto *inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeInt(f.arena, 10);
  inside->elements.push_back(range);

  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
