#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "simulator/clocking.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SyncDriveSim, OutputDriveZeroSkewSchedulesReNBA) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* out = f.ctx.CreateVariable("out_data", 8);
  out->value = MakeLogic4VecVal(f.arena, 8, 0);

  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};

  ClockingSignal sig;
  sig.signal_name = "out_data";
  sig.direction = ClockingDir::kOutput;
  block.signals.push_back(sig);
  cmgr.Register(block);
  cmgr.Attach(f.ctx, f.scheduler);

  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [&cmgr, &f]() {
    cmgr.ScheduleOutputDrive("cb", "out_data", 0xFE, f.ctx, f.scheduler);
  };
  f.scheduler.ScheduleEvent(SimTime{5}, Region::kActive, ev);
  f.scheduler.Run();

  EXPECT_EQ(out->value.ToUint64(), 0xFEu);
}

TEST(SyncDriveSim, OutputDriveWithNonzeroSkew) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* out = f.ctx.CreateVariable("data_out", 8);
  out->value = MakeLogic4VecVal(f.arena, 8, 0);

  ClockingManager cmgr;
  SetupClockingBlock(f, cmgr,
                     {"cb",
                      Edge::kPosedge,
                      {0},
                      SimTime{3},
                      "data_out",
                      ClockingDir::kOutput});

  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [&cmgr, &f]() {
    cmgr.ScheduleOutputDrive("cb", "data_out", 0x55, f.ctx, f.scheduler);
  };
  f.scheduler.ScheduleEvent(SimTime{10}, Region::kActive, ev);
  f.scheduler.Run();

  EXPECT_EQ(out->value.ToUint64(), 0x55u);
}

TEST(SyncDriveSim, SynchronousDriveSchedulesAtSkewOffset) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* out = f.ctx.CreateVariable("sync_out", 8);
  out->value = MakeLogic4VecVal(f.arena, 8, 0);

  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{2};

  ClockingSignal sig;
  sig.signal_name = "sync_out";
  sig.direction = ClockingDir::kOutput;
  block.signals.push_back(sig);
  cmgr.Register(block);
  cmgr.Attach(f.ctx, f.scheduler);

  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [&cmgr, &f]() {
    cmgr.ScheduleOutputDrive("cb", "sync_out", 0x42, f.ctx, f.scheduler);
  };
  f.scheduler.ScheduleEvent(SimTime{5}, Region::kActive, ev);
  f.scheduler.Run();

  EXPECT_EQ(out->value.ToUint64(), 0x42u);
}

TEST(SyncDriveSim, LastDriveWinsInSameTimestep) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* out = f.ctx.CreateVariable("nibble", 4);
  out->value = MakeLogic4VecVal(f.arena, 4, 0);

  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};

  ClockingSignal sig;
  sig.signal_name = "nibble";
  sig.direction = ClockingDir::kOutput;
  block.signals.push_back(sig);
  cmgr.Register(block);
  cmgr.Attach(f.ctx, f.scheduler);

  // Schedule two drives to the same output in the same timestep.
  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [&cmgr, &f]() {
    cmgr.ScheduleOutputDrive("cb", "nibble", 0x05, f.ctx, f.scheduler);
    cmgr.ScheduleOutputDrive("cb", "nibble", 0x03, f.ctx, f.scheduler);
  };
  f.scheduler.ScheduleEvent(SimTime{5}, Region::kActive, ev);
  f.scheduler.Run();

  // §14.16.2: Last value scheduled wins.
  EXPECT_EQ(out->value.ToUint64(), 0x03u);
}

}  // namespace
