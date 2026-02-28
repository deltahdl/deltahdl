// §14.10: Clocking block events

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

template <typename Fixture>
static void TestEdgeCallbackPosedge(Fixture& f) {
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
  uint32_t count = 0;
  cmgr.RegisterEdgeCallback("cb", f.ctx, f.scheduler, [&count]() { count++; });
  cmgr.Attach(f.ctx, f.scheduler);
  SchedulePosedge(f, clk, 10);
  ScheduleNegedge(f, clk, 15);
  SchedulePosedge(f, clk, 20);
  f.scheduler.Run();
  EXPECT_EQ(count, 2u);
}

namespace {

// =============================================================================
// 11. Clocking block events (@(cb)) (S14.8)
// =============================================================================
TEST(ClockingSim, ClockingBlockEvent) {
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

  auto* cb_event = f.ctx.CreateVariable("__cb_event", 1);
  cb_event->is_event = true;
  cmgr.SetBlockEventVar("cb", cb_event);

  cmgr.Attach(f.ctx, f.scheduler);

  bool triggered = false;
  cb_event->AddWatcher([&triggered]() {
    triggered = true;
    return true;
  });

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_TRUE(triggered);
}

// =============================================================================
// 18. Edge callback registration
// =============================================================================
TEST(ClockingSim, EdgeCallbackOnPosedge) {
  ClockingSimFixture f;
  TestEdgeCallbackPosedge(f);
}

// --- edge callback registration ---
TEST(SimA611, EdgeCallbackPosedge) {
  SimFixture f;
  TestEdgeCallbackPosedge(f);
}

}  // namespace
