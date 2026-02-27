// §18.13: Random number system functions and methods

#include "parser/ast.h"
#include "simulation/eval.h"

#include "fixture_simulator.h"
#include "builders_systask.h"

using namespace delta;

namespace {

TEST(SysTask, UrandomReturns32Bit) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$urandom", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

TEST(SysTask, UrandomRangeInBounds) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$urandom_range",
                         {MkInt(f.arena, 10), MkInt(f.arena, 5)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  uint64_t val = result.ToUint64();
  EXPECT_GE(val, 5u);
  EXPECT_LE(val, 10u);
}

}  // namespace
