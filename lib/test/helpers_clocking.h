#pragma once

#include <cstdint>

#include "fixture_simulator.h"
#include "simulation/clocking.h"

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

// Create a clocking block with one signal, register, and attach.
template <typename Fixture>
inline void SetupClockingBlock(
    Fixture& f, ClockingManager& cmgr,
    const char* block_name, Edge edge,
    SimTime input_skew, SimTime output_skew,
    const char* signal_name, ClockingDir signal_dir) {
  ClockingBlock block;
  block.name = block_name;
  block.clock_signal = "clk";
  block.clock_edge = edge;
  block.default_input_skew = input_skew;
  block.default_output_skew = output_skew;
  ClockingSignal sig;
  sig.signal_name = signal_name;
  sig.direction = signal_dir;
  block.signals.push_back(sig);
  cmgr.Register(block);
  cmgr.Attach(f.ctx, f.scheduler);
}
