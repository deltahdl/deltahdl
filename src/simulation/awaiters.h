#pragma once

#include <coroutine>
#include <cstdint>

#include "common/arena.h"
#include "common/types.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"

namespace delta {

// Awaiter for #N delay control. Suspends the coroutine and schedules a
// wakeup event at current_time + delay_ticks. For #0, targets the
// Inactive region per IEEE 1800-2023 §4.5.
struct DelayAwaiter {
  SimContext& ctx;
  uint64_t delay_ticks;

  bool await_ready() const noexcept { return false; }

  void await_suspend(std::coroutine_handle<> h) {
    auto time = ctx.CurrentTime() + SimTime{delay_ticks};
    auto region = (delay_ticks == 0) ? Region::kInactive : Region::kActive;
    auto* event = ctx.GetArena().Create<Event>();
    event->callback = [h]() mutable { h.resume(); };
    ctx.GetScheduler().ScheduleEvent(time, region, event);
  }

  void await_resume() const noexcept {}
};

}  // namespace delta
