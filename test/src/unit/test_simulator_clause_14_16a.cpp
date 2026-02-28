// §14.16: Synchronous drives

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
// 6. Clocking block output driving (S14.7)
// =============================================================================
TEST(ClockingSim, OutputDriving) {
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

// =============================================================================
// 10. Synchronous drives via clocking block (S14.14)
// =============================================================================
TEST(ClockingSim, SynchronousDriveSchedulesAtNextClock) {
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

}  // namespace
