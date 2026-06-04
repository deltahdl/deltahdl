#include <cstdint>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "simulator/clocking.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §14.16.1: although a synchronous drive reuses the nonblocking-assignment
// operator, a drive to an inout clockvar does not change the clocking block
// input. Reading the input always yields the last sampled value, never the
// value just driven. The simulator keeps these two faces of an inout signal
// apart: the output side is the live variable that ScheduleOutputDrive mutates
// in the Re-NBA region, while the input side is the sampled value captured at
// the clocking event and returned by GetSampledValue. Driving the output must
// therefore leave the sampled input untouched.
TEST(SyncDriveVsNba, InoutDriveDoesNotChangeSampledInput) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* a = f.ctx.CreateVariable("a", 8);
  a->value = MakeLogic4VecVal(f.arena, 8, 0xAA);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "a", ClockingDir::kInout});

  // The clocking event samples the inout's input side (0xAA). Once that event
  // has fired we drive the output side to a different value. Because the drive
  // matures in the Re-NBA region of the same event, it runs after sampling, so
  // any leak from the driven value into the sampled input would be observable.
  uint64_t sampled_before_drive = 0;
  cmgr.RegisterEdgeCallback("cb", f.ctx, f.scheduler, [&]() {
    sampled_before_drive = cmgr.GetSampledValue("cb", "a");
    cmgr.ScheduleOutputDrive("cb", "a", 0x55, f.ctx, f.scheduler);
  });

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  // The input read at the event yielded the sampled value, not the pending
  // drive value.
  EXPECT_EQ(sampled_before_drive, 0xAAu);
  // The output drive landed on the live variable...
  EXPECT_EQ(a->value.ToUint64(), 0x55u);
  // ...yet the clocking block input is unchanged: a read still returns the
  // sampled 0xAA, distinct from the driven 0x55.
  EXPECT_EQ(cmgr.GetSampledValue("cb", "a"), 0xAAu);
  EXPECT_NE(cmgr.GetSampledValue("cb", "a"), a->value.ToUint64());
}

// §14.16.1: because a drive never writes the clocking block input directly, the
// only way a driven value can ever reach the input is through the ordinary
// sampling that happens at the next clocking event. This test drives an inout in
// one cycle and confirms the input still reads the prior sampled value during
// that cycle, then sees the driven value appear at the input only after the
// following clocking event re-samples the (now driven) live signal. If the drive
// had touched the input itself, the first cycle's read would already differ.
TEST(SyncDriveVsNba, InoutInputReflectsDriveOnlyAfterNextSample) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* a = f.ctx.CreateVariable("a", 8);
  a->value = MakeLogic4VecVal(f.arena, 8, 0xAA);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "a", ClockingDir::kInout});

  uint64_t sampled_cycle1 = 0;
  uint64_t sampled_cycle2 = 0;
  int events = 0;
  cmgr.RegisterEdgeCallback("cb", f.ctx, f.scheduler, [&]() {
    ++events;
    if (events == 1) {
      // First clocking event: read the input (sampled 0xAA), then drive the
      // output side to a new value that matures this cycle.
      sampled_cycle1 = cmgr.GetSampledValue("cb", "a");
      cmgr.ScheduleOutputDrive("cb", "a", 0x55, f.ctx, f.scheduler);
    } else if (events == 2) {
      // Second clocking event: the input now reflects the driven value, but
      // only because this event re-sampled the live signal -- not because the
      // earlier drive wrote the input.
      sampled_cycle2 = cmgr.GetSampledValue("cb", "a");
    }
  });

  SchedulePosedge(f, clk, 10);
  ScheduleNegedge(f, clk, 15);
  SchedulePosedge(f, clk, 20);
  f.scheduler.Run();

  // During the drive's own cycle the input is unchanged by the drive.
  EXPECT_EQ(sampled_cycle1, 0xAAu);
  // The driven value reaches the input solely via the next event's sampling.
  EXPECT_EQ(sampled_cycle2, 0x55u);
  EXPECT_NE(sampled_cycle1, sampled_cycle2);
}

// §14.16.1: the worked example in the clause has an inout `a` and an output `b`
// in one clocking block, with `cb.a <= c` and `cb.b <= cb.a` driven together in
// the same block. Because a drive never updates the clocking block input, the
// `cb.a` read on the right-hand side of the second drive yields a's sampled
// input value -- the value it held *before* the concurrent drive to `cb.a`
// matures -- so `b` ends up with a's pre-drive value, not the value just driven
// onto a. This test models a two-clockvar block to confirm that an input read
// feeding another drive observes the sampled value rather than the pending one.
TEST(SyncDriveVsNba, InoutInputReadOnRhsYieldsSampledNotDrivenValue) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* a = f.ctx.CreateVariable("a", 8);
  a->value = MakeLogic4VecVal(f.arena, 8, 0xAA);
  auto* b = f.ctx.CreateVariable("b", 8);
  b->value = MakeLogic4VecVal(f.arena, 8, 0x00);

  // One block carrying both clockvars: `a` is inout (sampled on input, drivable
  // on output) and `b` is output-only. The single-signal helper cannot express
  // this, so the block is built directly.
  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  ClockingSignal sig_a;
  sig_a.signal_name = "a";
  sig_a.direction = ClockingDir::kInout;
  block.signals.push_back(sig_a);
  ClockingSignal sig_b;
  sig_b.signal_name = "b";
  sig_b.direction = ClockingDir::kOutput;
  block.signals.push_back(sig_b);
  cmgr.Register(block);
  cmgr.Attach(f.ctx, f.scheduler);

  uint64_t rhs_source = 0;
  cmgr.RegisterEdgeCallback("cb", f.ctx, f.scheduler, [&]() {
    // cb.a <= c : drive a's output side to a fresh value, maturing this cycle.
    cmgr.ScheduleOutputDrive("cb", "a", 0x55, f.ctx, f.scheduler);
    // cb.b <= cb.a : the right-hand side reads a's clocking block input, which
    // is the sampled value, unaffected by the drive scheduled just above.
    rhs_source = cmgr.GetSampledValue("cb", "a");
    cmgr.ScheduleOutputDrive("cb", "b", rhs_source, f.ctx, f.scheduler);
  });

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  // The RHS read saw a's sampled input, not the value being driven onto a.
  EXPECT_EQ(rhs_source, 0xAAu);
  // a's output drive matured to the new value...
  EXPECT_EQ(a->value.ToUint64(), 0x55u);
  // ...while b received a's pre-drive sampled value, distinct from a's driven
  // value -- exactly the clause's "value of a before the change" outcome.
  EXPECT_EQ(b->value.ToUint64(), 0xAAu);
  EXPECT_NE(b->value.ToUint64(), a->value.ToUint64());
}

}
