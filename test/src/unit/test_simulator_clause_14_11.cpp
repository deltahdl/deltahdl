// §14.11: Cycle delay: ##

#include <cstdint>
#include <string_view>

#include "common/types.h"
#include "parser/ast.h"
#include "simulator/clocking.h"
#include "simulator/variable.h"

#include "fixture_simulator.h"
#include "helpers_clocking.h"

using namespace delta;

// Helper fixture for clocking simulation tests.
// Schedule posedge at a given time through the scheduler.

// Schedule negedge at a given time through the scheduler.

namespace {

// =============================================================================
// 7. Cycle delay ##N (S14.11)
// =============================================================================
TEST(ClockingSim, CycleDelayWaitsNEdges) {
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

  auto* counter = f.ctx.CreateVariable("counter", 32);
  counter->value = MakeLogic4VecVal(f.arena, 32, 0);

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

}  // namespace
