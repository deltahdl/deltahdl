#include <cstdint>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "simulator/clocking.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Schedule a callback that records `var`'s current value into `dst` at `time`,
// run in the Postponed region so it observes any Re-NBA drive that matured in
// the same time step.
template <typename Fixture>
void ProbeAt(Fixture& f, Variable* var, uint64_t time, uint64_t* dst) {
  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [var, dst]() { *dst = var->value.ToUint64(); };
  f.scheduler.ScheduleEvent(SimTime{time}, Region::kPostponed, ev);
}

// §14.16.2: when more than one synchronous drive on the same clocking output is
// scheduled to mature in the same Re-NBA region of the same time step, only the
// last value is driven onto the signal. The drives here run coincident with the
// clocking event (inside the edge callback), matching the LRM nibble example
// where pe.nibble <= 4'b0101 followed by pe.nibble <= 4'b0011 yields 4'b0011.
TEST(SyncDriveSignals, LastDriveInSameReNBAWinsAtClockingEvent) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* nibble = f.ctx.CreateVariable("nibble", 4);
  nibble->value = MakeLogic4VecVal(f.arena, 4, 0);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"pe", Edge::kPosedge, {0}, {0}, "nibble", ClockingDir::kOutput});

  cmgr.RegisterEdgeCallback("pe", f.ctx, f.scheduler, [&]() {
    cmgr.ScheduleOutputDrive("pe", "nibble", 0x5, f.ctx, f.scheduler);
    cmgr.ScheduleOutputDrive("pe", "nibble", 0x3, f.ctx, f.scheduler);
  });

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_EQ(nibble->value.ToUint64(), 0x3u);
}

// §14.16.2: the last-value-wins rule holds whether the drives execute at a
// clocking event or at a time in between. Here both drives are issued from a
// plain event partway through the clock cycle; the later value still prevails.
TEST(SyncDriveSignals, LastDriveInSameReNBAWinsBetweenClockingEvents) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* nibble = f.ctx.CreateVariable("nibble", 4);
  nibble->value = MakeLogic4VecVal(f.arena, 4, 0);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"pe", Edge::kPosedge, {0}, {0}, "nibble", ClockingDir::kOutput});

  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [&]() {
    cmgr.ScheduleOutputDrive("pe", "nibble", 0x5, f.ctx, f.scheduler);
    cmgr.ScheduleOutputDrive("pe", "nibble", 0x3, f.ctx, f.scheduler);
  };
  f.scheduler.ScheduleEvent(SimTime{7}, Region::kActive, ev);
  f.scheduler.Run();

  EXPECT_EQ(nibble->value.ToUint64(), 0x3u);
}

// §14.16.2: when a single clocking output is driven by multiple synchronous
// drives scheduled to mature at different future times, each drive matures in
// its own cycle -- an earlier drive is not collapsed into or overwritten by a
// later one. The signal therefore shows value A after the first cycle and value
// B only after the second.
TEST(SyncDriveSignals, DrivesAtDifferentCyclesMatureIndependently) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* v = f.ctx.CreateVariable("v", 8);
  v->value = MakeLogic4VecVal(f.arena, 8, 0);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "v", ClockingDir::kOutput});

  int events = 0;
  cmgr.RegisterEdgeCallback("cb", f.ctx, f.scheduler, [&]() {
    ++events;
    if (events == 1)
      cmgr.ScheduleOutputDrive("cb", "v", 0xAA, f.ctx, f.scheduler);
    else if (events == 2)
      cmgr.ScheduleOutputDrive("cb", "v", 0xBB, f.ctx, f.scheduler);
  });

  uint64_t after_first = 0;
  uint64_t after_second = 0;
  SchedulePosedge(f, clk, 10);
  ProbeAt(f, v, 13, &after_first);
  // Return clk low so the second posedge is a genuine 0->1 edge.
  ScheduleNegedge(f, clk, 16);
  SchedulePosedge(f, clk, 20);
  ProbeAt(f, v, 25, &after_second);
  f.scheduler.Run();

  EXPECT_EQ(after_first, 0xAAu);
  EXPECT_EQ(after_second, 0xBBu);
}

// §14.16.2: when the same variable is an output of multiple clocking blocks on
// different clocking events, the last drive determines the variable's value;
// the variable takes on the value most recently assigned by either block. This
// models a multirate device whose two blocks (posedge and negedge) drive a
// shared signal. Between events -- in cycles with no synchronous drive -- the
// variable holds its previous value.
TEST(SyncDriveSignals, SharedOutputAcrossBlocksTakesMostRecentDrive) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* j = f.ctx.CreateVariable("j", 8);
  j->value = MakeLogic4VecVal(f.arena, 8, 0);

  ClockingManager cmgr;

  ClockingBlock pe;
  pe.name = "pe";
  pe.clock_signal = "clk";
  pe.clock_edge = Edge::kPosedge;
  ClockingSignal pe_sig;
  pe_sig.signal_name = "j";
  pe_sig.direction = ClockingDir::kOutput;
  pe.signals.push_back(pe_sig);
  cmgr.Register(pe);

  ClockingBlock ne;
  ne.name = "ne";
  ne.clock_signal = "clk";
  ne.clock_edge = Edge::kNegedge;
  ClockingSignal ne_sig;
  ne_sig.signal_name = "j";
  ne_sig.direction = ClockingDir::kOutput;
  ne.signals.push_back(ne_sig);
  cmgr.Register(ne);

  cmgr.Attach(f.ctx, f.scheduler);

  cmgr.RegisterEdgeCallback("pe", f.ctx, f.scheduler, [&]() {
    cmgr.ScheduleOutputDrive("pe", "j", 0x11, f.ctx, f.scheduler);
  });
  cmgr.RegisterEdgeCallback("ne", f.ctx, f.scheduler, [&]() {
    cmgr.ScheduleOutputDrive("ne", "j", 0x22, f.ctx, f.scheduler);
  });

  uint64_t after_posedge = 0;
  uint64_t after_negedge = 0;
  SchedulePosedge(f, clk, 10);
  ProbeAt(f, j, 12, &after_posedge);
  ScheduleNegedge(f, clk, 15);
  ProbeAt(f, j, 18, &after_negedge);
  f.scheduler.Run();

  // The posedge block drove 0x11; with no further drive the value persists to
  // the probe.
  EXPECT_EQ(after_posedge, 0x11u);
  // The negedge block's later drive replaces it: the variable holds the value
  // most recently assigned by either block.
  EXPECT_EQ(after_negedge, 0x22u);
}

// §14.16.2: a procedural assignment may target the signal underlying an output
// clockvar; the variable holds that value until another assignment occurs --
// either another procedural assignment or a synchronous drive to the clocking
// output. Here a procedural write sets the variable, it persists across a
// later probe, then a synchronous drive replaces it.
TEST(SyncDriveSignals, ProceduralValueHeldUntilSynchronousDrive) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* v = f.ctx.CreateVariable("v", 8);
  v->value = MakeLogic4VecVal(f.arena, 8, 0);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "v", ClockingDir::kOutput});

  cmgr.RegisterEdgeCallback("cb", f.ctx, f.scheduler, [&]() {
    cmgr.ScheduleOutputDrive("cb", "v", 0x77, f.ctx, f.scheduler);
  });

  // Procedural assignment to the underlying variable at time 5.
  auto* proc = f.scheduler.GetEventPool().Acquire();
  proc->callback = [&]() {
    v->value = MakeLogic4VecVal(f.arena, 8, 0x33);
  };
  f.scheduler.ScheduleEvent(SimTime{5}, Region::kActive, proc);

  uint64_t held = 0;
  uint64_t after_drive = 0;
  ProbeAt(f, v, 8, &held);
  SchedulePosedge(f, clk, 10);
  ProbeAt(f, v, 12, &after_drive);
  f.scheduler.Run();

  // The procedurally assigned value persists until the next assignment.
  EXPECT_EQ(held, 0x33u);
  // The synchronous drive at the clocking event then replaces it.
  EXPECT_EQ(after_drive, 0x77u);
}

// §14.16.2: when several clocking-block outputs drive the same net, each one is
// a driver on that net (the strong1/strong0 driver created per §14.16). Their
// values, together with any other drivers on the net, are resolved according to
// the net's type -- the clockvar drivers are ordinary participants in net
// resolution, not a last-writer-wins overwrite. Here two clocking-output
// drivers and one further driver are combined first on a wand and then a wor
// net; only the net type changes between the two resolutions, and the resolved
// value follows it.
TEST(SyncDriveSignals, MultipleClockingOutputsOnNetResolveByNetType) {
  ClockingSimFixture f;
  auto* n = f.ctx.CreateVariable("n", 4);
  n->value = MakeLogic4VecVal(f.arena, 4, 0);

  Net net;
  net.resolved = n;
  // Two drivers stand for two clocking outputs; both carry the (strong1,
  // strong0) strength §14.16 assigns to a clockvar net driver. The third
  // driver represents "any other drivers on the net."
  net.drivers.push_back(MakeLogic4VecVal(f.arena, 4, 0b0001));  // clocking out A
  net.drivers.push_back(MakeLogic4VecVal(f.arena, 4, 0b0001));  // clocking out B
  net.drivers.push_back(MakeLogic4VecVal(f.arena, 4, 0b0000));  // other driver
  net.driver_strengths.push_back(ClockvarNetDriverStrength());
  net.driver_strengths.push_back(ClockvarNetDriverStrength());
  net.driver_strengths.push_back(ClockvarNetDriverStrength());

  // wand: the lone 0 driver pulls the resolved value to 0.
  net.type = NetType::kWand;
  net.Resolve(f.arena);
  EXPECT_EQ(n->value.ToUint64() & 0xFu, 0b0000u);

  // wor on the identical driver set: the 1 drivers pull it to 1. The only
  // difference from the wand case is the net's type.
  net.type = NetType::kWor;
  net.Resolve(f.arena);
  EXPECT_EQ(n->value.ToUint64() & 0xFu, 0b0001u);
}

// §14.16.2: when a synchronous drive and a procedural nonblocking assignment
// write the same variable in the same time step, the writes are permitted to
// take place in an arbitrary order. This implementation realizes one such valid
// order -- the nonblocking assignment matures in the NBA region and the drive
// in the later Re-NBA region -- so both writes are applied (neither is dropped)
// and the drive's value is the one that survives.
TEST(SyncDriveSignals, DriveAndNonblockingAssignToSameVariableBothApply) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* v = f.ctx.CreateVariable("v", 8);
  v->value = MakeLogic4VecVal(f.arena, 8, 0);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr, {"cb", Edge::kPosedge, {0}, {0}, "v", ClockingDir::kOutput});

  bool nba_ran = false;
  cmgr.RegisterEdgeCallback("cb", f.ctx, f.scheduler, [&]() {
    // Synchronous drive of 0x55 -> matures in the Re-NBA region.
    cmgr.ScheduleOutputDrive("cb", "v", 0x55, f.ctx, f.scheduler);
    // Procedural nonblocking assignment of 0xAA to the same variable in the
    // same time step -> matures in the earlier NBA region.
    auto* nba = f.scheduler.GetEventPool().Acquire();
    nba->callback = [&]() {
      nba_ran = true;
      v->value = MakeLogic4VecVal(f.arena, 8, 0xAA);
    };
    f.scheduler.ScheduleEvent(f.scheduler.CurrentTime(), Region::kNBA, nba);
  });

  uint64_t after = 0;
  SchedulePosedge(f, clk, 10);
  ProbeAt(f, v, 12, &after);
  f.scheduler.Run();

  // The nonblocking write was applied...
  EXPECT_TRUE(nba_ran);
  // ...and the Re-NBA drive, ordered after it, is the surviving value.
  EXPECT_EQ(after, 0x55u);
}

}  // namespace
