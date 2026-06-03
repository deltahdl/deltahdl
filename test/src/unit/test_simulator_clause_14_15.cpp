#include <cstdint>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "parser/ast.h"
#include "simulator/clocking.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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

  // §14.15: the synchronization event control uses the synchronous values --
  // the values sampled at the corresponding clocking event -- not whatever the
  // live signal happens to hold when the waiting process resumes. To observe
  // that distinction the callback mutates the live variable before reading the
  // synchronous value back: the synchronized read must still see the sampled
  // 0xAA, while the live variable has already moved on to 0xFF.
  uint64_t sampled_at_event = 0;
  uint64_t live_at_event = 0;
  cmgr.RegisterEdgeCallback(
      "cb", f.ctx, f.scheduler, [&]() {
        data->value = MakeLogic4VecVal(f.arena, 8, 0xFF);
        sampled_at_event = cmgr.GetSampledValue("cb", "data");
        live_at_event = data->value.ToUint64();
      });

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_EQ(sampled_at_event, 0xAAu);
  EXPECT_EQ(live_at_event, 0xFFu);
  EXPECT_NE(sampled_at_event, live_at_event);
}

TEST(SyncEventSim, ResolveClockingMemberVariable) {
  ClockingSimFixture f;

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

TEST(SyncEventSim, ResolveClockingMemberMissingBackingVariable) {
  // §14.15: a synchronization event expression may name a clocking-block
  // input/inout, but resolving that member to a concrete object still requires
  // the underlying signal to exist in the simulation context. Here the member
  // is declared inside the block, yet no variable was ever created for it, so
  // resolution reports failure instead of fabricating a target.
  ClockingSimFixture f;
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

  // Deliberately skip CreateVariable("data", ...): the member is known to the
  // block but has no backing variable, exercising the resolve-to-null path.
  auto* resolved = cmgr.ResolveClockingMember("cb", "data", f.ctx);
  EXPECT_EQ(resolved, nullptr);
}

}
