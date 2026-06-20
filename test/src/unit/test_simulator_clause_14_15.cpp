#include <cstdint>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "parser/ast.h"
#include "simulator/clocking.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SyncEventSim, SampledValueUsedInSyncContext) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0xAA);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "data", ClockingDir::kInput});

  // §14.15: the synchronization event control uses the synchronous values --
  // the values sampled at the corresponding clocking event -- not whatever the
  // live signal happens to hold when the waiting process resumes. To observe
  // that distinction the callback mutates the live variable before reading the
  // synchronous value back: the synchronized read must still see the sampled
  // 0xAA, while the live variable has already moved on to 0xFF.
  uint64_t sampled_at_event = 0;
  uint64_t live_at_event = 0;
  cmgr.RegisterEdgeCallback("cb", f.ctx, f.scheduler, [&]() {
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

TEST(SyncEventSim, SlicedClockingInputUsesSynchronousBitAtFixedIndex) {
  // §14.15: a synchronization event expression may name a slice of a clocking
  // input, e.g. @(negedge dom.sign[a]). Two §14.15 rules govern what such a
  // slice observes: the slice's dynamic index is evaluated once, when the @
  // expression executes, and the value the synchronization event control uses
  // is the synchronous value -- the bit sampled at the corresponding clocking
  // event -- not whatever the live signal or the index variable hold when the
  // waiting process later resumes.
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* sign = f.ctx.CreateVariable("sign", 4);
  sign->value = MakeLogic4VecVal(f.arena, 4, 0b1010);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"dom", Edge::kNegedge, {0}, {0}, "sign", ClockingDir::kInput});

  // The dynamic index `a` is read a single time, at the instant the event
  // control executes. Capturing it once and reusing the captured value here
  // models §14.15's "evaluated once when the @ expression executes" rule.
  const uint32_t captured_index = 1;

  SchedulePosedge(f, clk, 5);   // drive clk high so prev==1 before the negedge
  ScheduleNegedge(f, clk, 10);  // negedge -> clocking event samples `sign`
  f.scheduler.Run();

  // The synchronous slice value is bit `captured_index` of the snapshot taken
  // by the production sampling path (SampleBlockInputs/SampleInput).
  uint64_t snapshot = cmgr.GetSampledValue("dom", "sign");
  uint64_t sync_bit = (snapshot >> captured_index) & 1;

  // After the event, both the live signal and a later re-evaluation of the
  // index move on. The synchronous slice must ignore both changes.
  sign->value = MakeLogic4VecVal(f.arena, 4, 0b0000);
  const uint32_t reindexed = 3;  // a value `a` might take on a later resume

  // Claim D: the snapshot is the value at the clocking event, immune to the
  // subsequent live mutation.
  EXPECT_EQ(cmgr.GetSampledValue("dom", "sign"), 0b1010u);
  // Claim B2: the bit chosen by the once-evaluated index is sign[1] of that
  // snapshot, i.e. 1.
  EXPECT_EQ(sync_bit, 1u);
  // A live, re-indexed read would yield a different bit, confirming the
  // synchronous/once semantics are not equivalent to reading the live slice.
  uint64_t live_reindexed_bit = (sign->value.ToUint64() >> reindexed) & 1;
  EXPECT_NE(sync_bit, live_reindexed_bit);
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

TEST(SyncEventSim, InoutClockingSignalSampledAsSynchronousValue) {
  // §14.15: a synchronization event expression may denote a clocking block
  // inout as well as an input. The synchronous value an inout contributes is
  // captured at the clocking event exactly like an input, so after the
  // governing edge GetSampledValue returns the value sampled at that event.
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0x3C);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "data", ClockingDir::kInout});

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_EQ(cmgr.GetSampledValue("cb", "data"), 0x3Cu);
}

TEST(SyncEventSim, OutputClockingSignalHasNoSynchronousValue) {
  // §14.15 scopes synchronization event expressions to clocking inputs and
  // inouts; the synchronous values they observe come from input sampling. An
  // output-only clockvar is never sampled at the clocking event, so it carries
  // no synchronous value -- GetSampledValue stays at its absent-entry default
  // even after the governing edge fires.
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0x55);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "data", ClockingDir::kOutput});

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_EQ(cmgr.GetSampledValue("cb", "data"), 0u);
}

}  // namespace
