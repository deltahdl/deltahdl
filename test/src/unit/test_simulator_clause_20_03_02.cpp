// §20.3.2: $stime

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

TEST(SysTask, StimeReturns32Bit) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$stime", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

}  // namespace
