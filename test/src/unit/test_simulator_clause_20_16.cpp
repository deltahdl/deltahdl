// §20.16: Programmable logic array modeling system tasks

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

TEST(SysTask, AsyncAndArrayReturnsZero) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$async$and$array", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
