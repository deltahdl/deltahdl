// §14.13: Input sampling

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "simulation/clocking.h"
#include "simulation/sim_context.h"

using namespace delta;

struct ClockingSimFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag, /*seed=*/42};
};

namespace {

TEST(Clocking, AttachSamplesOnClockEdge) {
  ClockingSimFixture f;
  auto *clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto *data_in = f.ctx.CreateVariable("data_in", 8);
  data_in->value = MakeLogic4VecVal(f.arena, 8, 0xAA);

  ClockingManager mgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.default_input_skew = SimTime{0};
  block.default_output_skew = SimTime{0};

  ClockingSignal sig;
  sig.signal_name = "data_in";
  sig.direction = ClockingDir::kInput;
  block.signals.push_back(sig);
  mgr.Register(block);

  mgr.Attach(f.ctx, f.scheduler);

  // Schedule clock posedge at t=10.
  auto *ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [&clk, &f]() {
    clk->value = MakeLogic4VecVal(f.arena, 1, 1);
    clk->NotifyWatchers();
  };
  f.scheduler.ScheduleEvent(SimTime{10}, Region::kActive, ev);

  f.scheduler.Run();

  // data_in should have been sampled.
  auto sampled = mgr.GetSampledValue("cb", "data_in");
  EXPECT_EQ(sampled, 0xAAu);
}

}  // namespace
