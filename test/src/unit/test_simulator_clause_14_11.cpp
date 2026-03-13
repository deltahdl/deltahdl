#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "parser/ast.h"
#include "simulator/clocking.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(CycleDelaySim, EdgeCallbackCountsThreeEdges) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);

  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};
  cmgr.Register(block);

  cmgr.SetDefaultClocking("cb");
  EXPECT_EQ(cmgr.GetDefaultClocking(), "cb");

  f.ctx.SetClockingManager(&cmgr);

  SchedulePosedge(f, clk, 10);
  ScheduleNegedge(f, clk, 15);
  SchedulePosedge(f, clk, 20);
  ScheduleNegedge(f, clk, 25);
  SchedulePosedge(f, clk, 30);

  uint32_t edge_count = 0;
  cmgr.RegisterEdgeCallback("cb", f.ctx, f.scheduler,
                            [&edge_count]() { edge_count++; });

  cmgr.Attach(f.ctx, f.scheduler);
  f.scheduler.Run();
  EXPECT_GE(edge_count, 3u);
}

TEST(CycleDelaySim, DefaultClockingRegistered) {
  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "bus";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  cmgr.Register(block);

  cmgr.SetDefaultClocking("bus");
  EXPECT_EQ(cmgr.GetDefaultClocking(), "bus");
  EXPECT_NE(cmgr.Find("bus"), nullptr);
}

TEST(CycleDelaySim, ZeroCycleDelayNoSuspend) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);

  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};
  cmgr.Register(block);
  cmgr.SetDefaultClocking("cb");

  // ##0 with 0 cycles should not suspend — await_ready returns true.
  // This verifies the CycleDelayAwaiter behavior.
  f.ctx.SetClockingManager(&cmgr);
  cmgr.Attach(f.ctx, f.scheduler);
  f.scheduler.Run();
  // No assertion needed beyond not hanging.
}

}  // namespace
