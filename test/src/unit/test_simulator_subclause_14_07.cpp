#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "parser/ast.h"
#include "simulator/clocking.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ClockingScopeSim, BlockPersistsAcrossClockEdges) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0x10);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "data", ClockingDir::kInput});

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();
  EXPECT_EQ(cmgr.GetSampledValue("cb", "data"), 0x10u);

  data->value = MakeLogic4VecVal(f.arena, 8, 0x20);
  // The clock returns low by changing value, which is how a clock returns low.
  // Writing clk->value straight down leaves the block's record of it saying
  // high, so the edge at 20 is no edge at all -- and it read as one only while
  // the block took its record from a field the test helper wrote.
  ScheduleNegedge(f, clk, 15);
  SchedulePosedge(f, clk, 20);
  f.scheduler.Run();
  EXPECT_EQ(cmgr.GetSampledValue("cb", "data"), 0x20u);
}

}  // namespace
