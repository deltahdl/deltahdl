#pragma once

#include <coroutine>
#include <cstdint>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/variable.h"

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

// Awaiter for @(posedge/negedge/any-change) event control. Suspends the
// coroutine until the specified edge condition is detected on any of the
// watched signals.
struct EventAwaiter {
  SimContext& ctx;
  const std::vector<EventExpr>& events;

  bool await_ready() const noexcept { return false; }

  void await_suspend(std::coroutine_handle<> h) {
    for (const auto& ev : events) {
      if (!ev.signal || ev.signal->kind != ExprKind::kIdentifier) continue;
      auto* var = ctx.FindVariable(ev.signal->text);
      if (!var) continue;
      var->prev_value = var->value;
      Edge edge = ev.edge;
      var->AddWatcher([h, var, edge]() mutable {
        bool trigger = CheckEdge(var, edge);
        if (trigger) h.resume();
      });
    }
  }

  void await_resume() const noexcept {}

  static bool CheckEdge(const Variable* var, Edge edge) {
    uint64_t prev = var->prev_value.ToUint64();
    uint64_t cur = var->value.ToUint64();
    if (edge == Edge::kPosedge) return (prev & 1) == 0 && (cur & 1) == 1;
    if (edge == Edge::kNegedge) return (prev & 1) == 1 && (cur & 1) == 0;
    return prev != cur;  // any change
  }
};

// Awaiter that watches a set of variables and resumes on any value change.
// Used for always_comb sensitivity inference.
struct AnyChangeAwaiter {
  SimContext& ctx;
  const std::vector<std::string_view>& var_names;

  bool await_ready() const noexcept { return false; }

  void await_suspend(std::coroutine_handle<> h) {
    for (auto name : var_names) {
      auto* var = ctx.FindVariable(name);
      if (!var) continue;
      var->prev_value = var->value;
      var->AddWatcher([h]() mutable { h.resume(); });
    }
  }

  void await_resume() const noexcept {}
};

}  // namespace delta
