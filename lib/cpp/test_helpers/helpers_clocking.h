#pragma once

#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_simulator.h"
#include "simulator/clocking.h"

using namespace delta;

template <typename Fixture>
inline void SchedulePosedge(Fixture& f, Variable* clk, uint64_t time) {
  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [clk, &f]() {
    clk->prev_value = clk->value;
    clk->value = MakeLogic4VecVal(f.arena, 1, 1);
    clk->NotifyWatchers();
  };
  f.scheduler.ScheduleEvent(SimTime{time}, Region::kActive, ev);
}

template <typename Fixture>
inline void ScheduleNegedge(Fixture& f, Variable* clk, uint64_t time) {
  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [clk, &f]() {
    clk->prev_value = clk->value;
    clk->value = MakeLogic4VecVal(f.arena, 1, 0);
    clk->NotifyWatchers();
  };
  f.scheduler.ScheduleEvent(SimTime{time}, Region::kActive, ev);
}

struct ClockingSetupParams {
  const char* block_name;
  Edge edge;
  SimTime input_skew;
  SimTime output_skew;
  const char* signal_name;
  ClockingDir signal_dir;
  // Marks the signal's own skew as a written #0 rather than an unset default.
  // §14.13 samples a #0 input in the Observed region and any other input in
  // the Postponed region, so the distinction between "zero" and "not written"
  // is what a sampling test turns on.
  bool explicit_zero_skew = false;
};

// Create a clocking block with one signal, register, and attach.
template <typename Fixture>
inline void SetupClockingBlock(Fixture& f, ClockingManager& cmgr,
                               const ClockingSetupParams& p) {
  ClockingBlock block;
  block.name = p.block_name;
  block.clock_signal = "clk";
  block.clock_edge = p.edge;
  block.default_input_skew = p.input_skew;
  block.default_output_skew = p.output_skew;
  ClockingSignal sig;
  sig.signal_name = p.signal_name;
  sig.direction = p.signal_dir;
  if (p.explicit_zero_skew) {
    sig.skew = SimTime{0};
    sig.is_explicit_zero_skew = true;
  }
  block.signals.push_back(sig);
  cmgr.Register(block);
  cmgr.Attach(f.ctx, f.scheduler);
}

// Full output-drive test: create clk + data_out, setup an output clocking block
// with skew 5, schedule a drive of drive_val at t=10, run, and verify data_out
// holds drive_val afterward.
template <typename Fixture>
inline void TestOutputSkewDrive(Fixture& f, ClockingManager& cmgr,
                                uint64_t drive_val) {
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 0);
  auto* data_out = f.ctx.CreateVariable("data_out", 8);
  data_out->value = MakeLogic4VecVal(f.arena, 8, 0);

  SetupClockingBlock(f, cmgr,
                     {"cb",
                      Edge::kPosedge,
                      {0},
                      SimTime{5},
                      "data_out",
                      ClockingDir::kOutput});

  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [&cmgr, &f, drive_val]() {
    cmgr.ScheduleOutputDrive("cb", "data_out", drive_val, f.ctx, f.scheduler);
  };
  f.scheduler.ScheduleEvent(SimTime{10}, Region::kActive, ev);
  f.scheduler.Run();

  EXPECT_EQ(data_out->value.ToUint64(), drive_val);
}

// Full negedge sampling test: create clk + data, setup clocking, schedule
// negedge, run, verify sampled value.
template <typename Fixture>
inline void TestNegedgeSampling(Fixture& f, ClockingManager& cmgr) {
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, 1);
  auto* data = f.ctx.CreateVariable("neg_data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0xDD);
  SetupClockingBlock(
      f, cmgr,
      {"cb_neg", Edge::kNegedge, {0}, {0}, "neg_data", ClockingDir::kInput});
  ScheduleNegedge(f, clk, 10);
  f.scheduler.Run();
  EXPECT_EQ(cmgr.GetSampledValue("cb_neg", "neg_data"), 0xDDu);
}

// The clock and the one signal a sampling test starts from: `clk` holds
// `clk_value` so an edge can be scheduled onto it, and the signal holds the
// value the first clocking event is meant to sample.
struct ClockAndSignal {
  Variable* clk;
  Variable* signal;
};

template <typename Fixture>
inline ClockAndSignal CreateClockAndSignal(Fixture& f, uint64_t clk_value,
                                           const char* signal_name,
                                           uint32_t signal_width,
                                           uint64_t signal_value) {
  auto* clk = f.ctx.CreateVariable("clk", 1);
  clk->value = MakeLogic4VecVal(f.arena, 1, clk_value);
  auto* signal = f.ctx.CreateVariable(signal_name, signal_width);
  signal->value = MakeLogic4VecVal(f.arena, signal_width, signal_value);
  return {clk, signal};
}

// Schedules `var` taking `value` in the Active region at `time`, which is how
// a test puts a signal change beside a clocking event without a process to
// carry it.
template <typename Fixture>
inline void ScheduleValueChange(Fixture& f, Variable* var, uint64_t time,
                                uint64_t value) {
  auto* ev = f.scheduler.GetEventPool().Acquire();
  ev->callback = [var, value, &f]() {
    var->value = MakeLogic4VecVal(f.arena, var->value.width, value);
  };
  f.scheduler.ScheduleEvent(SimTime{time}, Region::kActive, ev);
}
