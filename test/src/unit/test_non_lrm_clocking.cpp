// Non-LRM tests

#include <gtest/gtest.h>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "simulation/clocking.h"
#include "simulation/sim_context.h"

using namespace delta;

namespace {

// =============================================================================
// ClockingBlock registration
// =============================================================================
TEST(Clocking, RegisterAndFind) {
  ClockingManager mgr;
  ClockingBlock block;
  block.name = "cb_main";
  block.clock_signal = "clk";
  block.default_input_skew = SimTime{2};
  block.default_output_skew = SimTime{3};

  mgr.Register(block);
  EXPECT_EQ(mgr.Count(), 1u);

  const auto* found = mgr.Find("cb_main");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->clock_signal, "clk");
  EXPECT_EQ(found->default_input_skew.ticks, 2u);
}

TEST(Clocking, FindNonexistent) {
  ClockingManager mgr;
  EXPECT_EQ(mgr.Find("nonexistent"), nullptr);
}

// =============================================================================
// Skew resolution
// =============================================================================
TEST(Clocking, DefaultInputSkew) {
  ClockingManager mgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.default_input_skew = SimTime{5};
  block.default_output_skew = SimTime{10};
  mgr.Register(block);

  // No per-signal skew, should return default.
  auto skew = mgr.GetInputSkew("cb", "data_in");
  EXPECT_EQ(skew.ticks, 5u);
}

TEST(Clocking, PerSignalSkewOverridesDefault) {
  ClockingManager mgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.default_input_skew = SimTime{5};
  block.default_output_skew = SimTime{10};

  ClockingSignal sig;
  sig.signal_name = "data_in";
  sig.direction = ClockingDir::kInput;
  sig.skew = SimTime{7};
  block.signals.push_back(sig);

  mgr.Register(block);

  auto skew = mgr.GetInputSkew("cb", "data_in");
  EXPECT_EQ(skew.ticks, 7u);

  // Unknown signal falls back to default.
  auto default_skew = mgr.GetInputSkew("cb", "other_signal");
  EXPECT_EQ(default_skew.ticks, 5u);
}

TEST(Clocking, OutputSkew) {
  ClockingManager mgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.default_input_skew = SimTime{1};
  block.default_output_skew = SimTime{3};
  mgr.Register(block);

  auto skew = mgr.GetOutputSkew("cb", "data_out");
  EXPECT_EQ(skew.ticks, 3u);
}

TEST(Clocking, AttachSamplesOnClockEdge) {
  ClockingSimFixture f;
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data_in = f.ctx.CreateVariable("data_in", 8);
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
  auto* ev = f.scheduler.GetEventPool().Acquire();
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
