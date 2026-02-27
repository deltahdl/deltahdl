// §20.15: Stochastic analysis tasks and functions

#include "parser/ast.h"
#include "simulation/eval.h"

#include "fixture_simulator.h"
#include "builders_systask.h"

using namespace delta;

namespace {

TEST(SysTask, QInitializeReturnsZero) {
  SysTaskFixture f;
  auto* expr =
      MkSysCall(f.arena, "$q_initialize",
                {MkInt(f.arena, 1), MkInt(f.arena, 1), MkInt(f.arena, 100)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(SysTask, QFullReturnsZero) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$q_full", {MkInt(f.arena, 1)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
