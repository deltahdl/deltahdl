#pragma once

#include <coroutine>
#include <cstdint>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/scheduler.h"
#include "simulator/clocking.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

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
    auto region = SelectDelayRegion();
    auto* event = ctx.GetScheduler().GetEventPool().Acquire();
    event->callback = [h]() mutable { h.resume(); };
    ctx.GetScheduler().ScheduleEvent(time, region, event);
  }

  Region SelectDelayRegion() const {
    if (delay_ticks != 0) return Region::kActive;
    return ctx.IsReactiveContext() ? Region::kReInactive : Region::kInactive;
  }

  void await_resume() const noexcept {}
};

// Awaiter for @(posedge/negedge/any-change) event control. Suspends the
// coroutine until the specified edge condition is detected on any of the
// watched signals.
struct EventAwaiter {
  SimContext& ctx;
  const std::vector<EventExpr>& events;
  Arena& arena;

  bool await_ready() const noexcept { return false; }

  void await_suspend(std::coroutine_handle<> h) {
    for (const auto& ev : events) {
      if (!ev.signal) continue;
      Variable* var = nullptr;
      if (ev.signal->kind == ExprKind::kIdentifier) {
        var = ctx.FindVariable(ev.signal->text);
      } else if (ev.signal->kind == ExprKind::kMemberAccess && ev.signal->lhs &&
                 ev.signal->lhs->kind == ExprKind::kIdentifier) {
        // §14.15: @(cb.signal) — resolve through clocking manager.
        auto* mgr = ctx.GetClockingManager();
        std::string_view member;
        if (ev.signal->rhs && ev.signal->rhs->kind == ExprKind::kIdentifier)
          member = ev.signal->rhs->text;
        else if (!ev.signal->text.empty())
          member = ev.signal->text;
        if (mgr && !member.empty())
          var = mgr->ResolveClockingMember(ev.signal->lhs->text, member, ctx);
        if (!var) var = ctx.FindVariable(ev.signal->lhs->text);
      } else {
        continue;
      }
      if (!var) continue;
      if (var->is_event) {
        var->AddWatcher([h]() mutable {
          h.resume();
          return true;
        });
        continue;
      }
      var->prev_value = var->value;
      auto* ctx_ptr = &ctx;
      var->AddWatcher([h, var, edge = ev.edge, iff_cond = ev.iff_condition,
                       ctx_ptr]() mutable {
        return HandleEdgeEvent(h, var, edge, iff_cond, *ctx_ptr);
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

  static bool HandleEdgeEvent(std::coroutine_handle<>& h, Variable* var,
                              Edge edge, const Expr* iff_cond,
                              SimContext& ctx) {
    if (!CheckEdge(var, edge)) {
      var->prev_value = var->value;
      return false;
    }
    if (iff_cond) {
      auto val = EvalExpr(iff_cond, ctx, ctx.GetArena());
      if (val.ToUint64() == 0) {
        var->prev_value = var->value;
        return false;
      }
    }
    h.resume();
    return true;
  }
};

// Awaiter for named event wait (@ev). Suspends the coroutine until the
// event variable is triggered via ->ev (NotifyWatchers). No edge check;
// resumes unconditionally on trigger.
struct NamedEventAwaiter {
  SimContext& ctx;
  std::string_view event_name;

  bool await_ready() const noexcept { return false; }

  void await_suspend(std::coroutine_handle<> h) {
    auto* var = ctx.FindVariable(event_name);
    if (!var) return;
    var->AddWatcher([h]() mutable {
      h.resume();
      return true;
    });
  }

  void await_resume() const noexcept {}
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
      var->AddWatcher([h]() mutable {
        h.resume();
        return true;
      });
    }
  }

  void await_resume() const noexcept {}
};

// Shared state for fork/join synchronization.
struct ForkJoinState {
  uint32_t remaining = 0;
  std::coroutine_handle<> parent;
  bool join_any = false;
  bool resumed = false;
};

// Awaiter for fork/join and fork/join_any. Suspends the parent coroutine
// until all (join) or any (join_any) children complete.
struct ForkJoinAwaiter {
  ForkJoinState* state;

  bool await_ready() const noexcept { return state->remaining == 0; }

  void await_suspend(std::coroutine_handle<> h) noexcept { state->parent = h; }

  void await_resume() const noexcept {}
};

// Awaiter for ##N cycle delay. Suspends the coroutine until N clocking
// block events have occurred on the default clocking block.
struct CycleDelayAwaiter {
  SimContext& ctx;
  uint32_t cycles;

  bool await_ready() const noexcept { return cycles == 0; }

  void await_suspend(std::coroutine_handle<> h) {
    auto* mgr = ctx.GetClockingManager();
    if (!mgr) {
      h.resume();
      return;
    }
    auto block_name = mgr->GetDefaultClocking();
    if (block_name.empty()) {
      h.resume();
      return;
    }
    auto* counter = new uint32_t(cycles);
    mgr->RegisterEdgeCallback(
        block_name, ctx, ctx.GetScheduler(),
        [h, counter]() mutable {
          if (*counter > 0) --(*counter);
          if (*counter == 0) {
            delete counter;
            h.resume();
          }
        });
  }

  void await_resume() const noexcept {}
};

}  // namespace delta
