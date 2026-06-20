#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "parser/ast.h"
#include "simulator/clocking.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ClockingHierExprSim, HierarchicalSignalSampled) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data_in", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0xCC);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr,
      {"cb", Edge::kPosedge, {0}, {0}, "data_in", ClockingDir::kInput});

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  auto sampled = cmgr.GetSampledValue("cb", "data_in");
  EXPECT_EQ(sampled, 0xCCu);
}

TEST(ClockingHierExprSim, OutputHierSignalDriven) {
  ClockingSimFixture f;
  ClockingManager cmgr;
  TestOutputSkewDrive(f, cmgr, 0xBEu);
}

TEST(ClockingHierExprSim, InoutHierSignalBidirectional) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* bidir = f.ctx.CreateVariable("bidir", 8);
  bidir->value = MakeLogic4VecVal(f.arena, 8, 0xEE);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr,
      {"cb", Edge::kPosedge, {0}, SimTime{2}, "bidir", ClockingDir::kInout});

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_EQ(cmgr.GetSampledValue("cb", "bidir"), 0xEEu);

  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [&cmgr, &f]() {
    cmgr.ScheduleOutputDrive("cb", "bidir", 0x11, f.ctx, f.scheduler);
  };
  f.scheduler.ScheduleEvent(SimTime{20}, Region::kActive, ev);
  f.scheduler.Run();
  EXPECT_EQ(bidir->value.ToUint64(), 0x11u);
}

}  // namespace
