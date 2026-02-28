// §20.4: Timescale system tasks and system functions

#include "parser/ast.h"
#include "simulator/eval.h"

#include "fixture_simulator.h"
#include "builders_systask.h"

using namespace delta;

namespace {

TEST(SysTask, PrinttimescaleDoesNotCrash) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$printtimescale", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

TEST(SysTask, TimeformatDoesNotCrash) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$timeformat",
                         {MkInt(f.arena, 0), MkInt(f.arena, 0),
                          MkStr(f.arena, " ns"), MkInt(f.arena, 10)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

}  // namespace
