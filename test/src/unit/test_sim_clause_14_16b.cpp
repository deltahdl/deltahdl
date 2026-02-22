// §14.16: Synchronous drives

#include <gtest/gtest.h>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "simulation/clocking.h"
#include "simulation/sim_context.h"

using namespace delta;

namespace {

TEST(Clocking, ScheduleOutputDrive) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data_out = f.ctx.CreateVariable("data_out", 8);
  data_out->value = MakeLogic4VecVal(f.arena, 8, 0);

  ClockingManager mgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{3};

  ClockingSignal sig;
  sig.signal_name = "data_out";
  sig.direction = ClockingDir::kOutput;
  block.signals.push_back(sig);
  mgr.Register(block);

  mgr.Attach(f.ctx, f.scheduler);

  // At t=10, drive output value 0x55.
  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [&mgr, &f]() {
    mgr.ScheduleOutputDrive("cb", "data_out", 0x55, f.ctx, f.scheduler);
  };
  f.scheduler.ScheduleEvent(SimTime{10}, Region::kActive, ev);

  f.scheduler.Run();

  // data_out should be updated at t=13 (10 + 3 output skew).
  EXPECT_EQ(data_out->value.ToUint64(), 0x55u);
}

}  // namespace
