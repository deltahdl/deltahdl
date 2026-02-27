// §20.9: Bit vector system functions

#include "parser/ast.h"
#include "simulation/eval.h"

#include "fixture_simulator.h"
#include "builders_systask.h"

using namespace delta;

namespace {

TEST(SysTask, CountbitsMatchingPattern) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$countbits",
                         {MkInt(f.arena, 0xA5), MkInt(f.arena, 1)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 4u);
}

}  // namespace
