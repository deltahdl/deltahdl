// Non-LRM tests

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

TEST(EvalOp, InsideRangeNoMatch) {
  SimFixture f;
  // 10 inside {[3:7]} = 0
  auto* range = f.arena.Create<Expr>();
  range->kind = ExprKind::kSelect;
  range->index = MakeInt(f.arena, 3);
  range->index_end = MakeInt(f.arena, 7);

  auto* inside = f.arena.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->lhs = MakeInt(f.arena, 10);
  inside->elements.push_back(range);

  auto result = EvalExpr(inside, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
