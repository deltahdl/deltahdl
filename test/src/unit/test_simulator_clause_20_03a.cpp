// §20.3: Simulation time system functions

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

TEST(SysTask, TimeReturnsCurrentTicks) {
  SysTaskFixture f;
  auto* event = f.scheduler.GetEventPool().Acquire();
  event->callback = []() {};
  f.scheduler.ScheduleEvent(SimTime{100}, Region::kActive, event);
  auto* expr = MkSysCall(f.arena, "$time", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
  EXPECT_EQ(result.width, 64u);
}

TEST(SysTask, StimeReturns32Bit) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$stime", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

TEST(SysTask, RealtimeReturns64Bit) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$realtime", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 64u);
}

}  // namespace
