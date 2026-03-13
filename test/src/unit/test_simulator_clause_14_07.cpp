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
      f, cmgr,
      {"cb", Edge::kPosedge, {0}, {0}, "data", ClockingDir::kInput});

  // First edge: sample 0x10.
  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();
  EXPECT_EQ(cmgr.GetSampledValue("cb", "data"), 0x10u);

  // Change data and trigger second edge: block still alive.
  data->value = MakeLogic4VecVal(f.arena, 8, 0x20);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);  // Reset for negedge->posedge.
  SchedulePosedge(f, clk, 20);
  f.scheduler.Run();
  EXPECT_EQ(cmgr.GetSampledValue("cb", "data"), 0x20u);
}

TEST(ClockingScopeSim, DotAccessRetrievesSampledValue) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* sig = f.ctx.CreateVariable("sig", 8);
  sig->value = MakeLogic4VecVal(f.arena, 8, 0xBB);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr,
      {"dom", Edge::kPosedge, {0}, {0}, "sig", ClockingDir::kInput});

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  // Simulates dom.sig access.
  EXPECT_EQ(cmgr.GetSampledValue("dom", "sig"), 0xBBu);
}

}  // namespace
