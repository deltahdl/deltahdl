#include <cstdint>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "parser/ast.h"
#include "simulator/clocking.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SyncEventSim, WaitForClockingBlockEvent) {
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

  // Create block event variable and register it.
  auto* ev_var = f.ctx.CreateVariable("cb", 1);
  ev_var->is_event = true;
  cmgr.SetBlockEventVar("cb", ev_var);
  cmgr.Attach(f.ctx, f.scheduler);

  // Track if watcher fires.
  bool event_fired = false;
  ev_var->AddWatcher([&event_fired]() {
    event_fired = true;
    return true;
  });

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();
  EXPECT_TRUE(event_fired);
}

TEST(SyncEventSim, ClockingSignalChangeDetected) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0x00);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr,
      {"cb", Edge::kPosedge, {0}, {0}, "data", ClockingDir::kInput});
  cmgr.Attach(f.ctx, f.scheduler);

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  // After posedge, data was sampled.
  EXPECT_EQ(cmgr.GetSampledValue("cb", "data"), 0x00u);
}

TEST(SyncEventSim, SampledValueUsedInSyncContext) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0xAA);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr,
      {"cb", Edge::kPosedge, {0}, {0}, "data", ClockingDir::kInput});

  // Register edge callback to capture sampled value after block event.
  uint64_t sampled_at_event = 0;
  cmgr.RegisterEdgeCallback("cb", f.ctx, f.scheduler,
                            [&cmgr, &sampled_at_event]() {
                              sampled_at_event =
                                  cmgr.GetSampledValue("cb", "data");
                            });

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_EQ(sampled_at_event, 0xAAu);
}

TEST(SyncEventSim, ResolveClockingMemberVariable) {
  ClockingSimFixture f;
  // Simulate resolving "cb.data" -> underlying variable "data".
  auto* data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0x55);

  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  ClockingSignal sig;
  sig.signal_name = "data";
  sig.direction = ClockingDir::kInput;
  block.signals.push_back(sig);
  cmgr.Register(block);

  // ResolveClockingMember should find the underlying variable.
  auto* resolved = cmgr.ResolveClockingMember("cb", "data", f.ctx);
  ASSERT_NE(resolved, nullptr);
  EXPECT_EQ(resolved->value.ToUint64(), 0x55u);
}

TEST(SyncEventSim, ResolveClockingMemberUnknownBlock) {
  ClockingSimFixture f;
  ClockingManager cmgr;
  auto* resolved = cmgr.ResolveClockingMember("nonexistent", "data", f.ctx);
  EXPECT_EQ(resolved, nullptr);
}

TEST(SyncEventSim, ResolveClockingMemberUnknownSignal) {
  ClockingSimFixture f;
  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  cmgr.Register(block);

  auto* resolved = cmgr.ResolveClockingMember("cb", "nonexistent", f.ctx);
  EXPECT_EQ(resolved, nullptr);
}

}  // namespace
