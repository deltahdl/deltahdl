// §18.13.2: $urandom_range()

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

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
