#include <gtest/gtest.h>

#include <cstdint>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "parser/ast_stmt.h"
#include "simulator/clocking.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

template <typename Fixture>
void ProbeAt(Fixture& f, Variable* var, uint64_t time, uint64_t* dst) {
  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [var, dst]() { *dst = var->value.ToUint64(); };
  f.scheduler.ScheduleEvent(SimTime{time}, Region::kPostponed, ev);
}

TEST(SyncDriveSignals, LastDriveInSameReNBAWinsAtClockingEvent) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* nibble = f.ctx.CreateVariable("nibble", 4);
  nibble->value = MakeLogic4VecVal(f.arena, 4, 0);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr,
      {"pe", Edge::kPosedge, {0}, {0}, "nibble", ClockingDir::kOutput});

  cmgr.RegisterEdgeCallback("pe", f.ctx, f.scheduler, [&]() {
    cmgr.ScheduleOutputDrive("pe", "nibble", 0x5, f.ctx, f.scheduler);
    cmgr.ScheduleOutputDrive("pe", "nibble", 0x3, f.ctx, f.scheduler);
  });

  SchedulePosedge(f, clk, 10);
  f.scheduler.Run();

  EXPECT_EQ(nibble->value.ToUint64(), 0x3u);
}

TEST(SyncDriveSignals, LastDriveInSameReNBAWinsBetweenClockingEvents) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* nibble = f.ctx.CreateVariable("nibble", 4);
  nibble->value = MakeLogic4VecVal(f.arena, 4, 0);

  ClockingManager cmgr;
  SetupClockingBlock(
      f, cmgr,
      {"pe", Edge::kPosedge, {0}, {0}, "nibble", ClockingDir::kOutput});

  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [&]() {
    cmgr.ScheduleOutputDrive("pe", "nibble", 0x5, f.ctx, f.scheduler);
    cmgr.ScheduleOutputDrive("pe", "nibble", 0x3, f.ctx, f.scheduler);
  };
  f.scheduler.ScheduleEvent(SimTime{7}, Region::kActive, ev);
  f.scheduler.Run();

  EXPECT_EQ(nibble->value.ToUint64(), 0x3u);
}

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
  ScheduleNegedge(f, clk, 16);
  SchedulePosedge(f, clk, 20);
  ProbeAt(f, v, 25, &after_second);
  f.scheduler.Run();

  EXPECT_EQ(after_first, 0xAAu);
  EXPECT_EQ(after_second, 0xBBu);
}

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

  EXPECT_EQ(after_posedge, 0x11u);
  EXPECT_EQ(after_negedge, 0x22u);
}

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

  auto* proc = f.scheduler.GetEventPool().Acquire();
  proc->callback = [&]() { v->value = MakeLogic4VecVal(f.arena, 8, 0x33); };
  f.scheduler.ScheduleEvent(SimTime{5}, Region::kActive, proc);

  uint64_t held = 0;
  uint64_t after_drive = 0;
  ProbeAt(f, v, 8, &held);
  SchedulePosedge(f, clk, 10);
  ProbeAt(f, v, 12, &after_drive);
  f.scheduler.Run();

  EXPECT_EQ(held, 0x33u);
  EXPECT_EQ(after_drive, 0x77u);
}

TEST(SyncDriveSignals, MultipleClockingOutputsOnNetResolveByNetType) {
  ClockingSimFixture f;
  auto* n = f.ctx.CreateVariable("n", 4);
  n->value = MakeLogic4VecVal(f.arena, 4, 0);

  Net net;
  net.resolved = n;
  net.drivers.push_back(MakeLogic4VecVal(f.arena, 4, 0b0001));
  net.drivers.push_back(MakeLogic4VecVal(f.arena, 4, 0b0001));
  net.drivers.push_back(MakeLogic4VecVal(f.arena, 4, 0b0000));
  net.driver_strengths.push_back(ClockvarNetDriverStrength());
  net.driver_strengths.push_back(ClockvarNetDriverStrength());
  net.driver_strengths.push_back(ClockvarNetDriverStrength());

  net.type = NetType::kWand;
  net.Resolve(f.arena);
  EXPECT_EQ(n->value.ToUint64() & 0xFu, 0b0000u);

  net.type = NetType::kWor;
  net.Resolve(f.arena);
  EXPECT_EQ(n->value.ToUint64() & 0xFu, 0b0001u);
}

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
    cmgr.ScheduleOutputDrive("cb", "v", 0x55, f.ctx, f.scheduler);
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

  EXPECT_TRUE(nba_ran);
  EXPECT_EQ(after, 0x55u);
}

}  // namespace
