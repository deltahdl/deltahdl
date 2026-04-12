#pragma once

#include <coroutine>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "parser/ast.h"
#include "simulator/process.h"
#include "simulator/evaluation.h"
#include "simulator/scheduler.h"
#include "simulator/clocking.h"
#include "simulator/sim_context.h"
#include "simulator/sync_objects.h"
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
    auto* proc = ctx.CurrentProcess();
    event->callback = [h, proc, &ctx]() mutable {
      if (proc && !proc->active) return;
      if (proc) ctx.SetCurrentProcess(proc);
      h.resume();
    };
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
    auto* proc = ctx.CurrentProcess();
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
        var->AddWatcher([h, proc]() mutable {
          if (proc && !proc->active) return true;
          h.resume();
          return true;
        });
        continue;
      }
      var->prev_value = var->value;
      auto* ctx_ptr = &ctx;
      var->AddWatcher([h, var, edge = ev.edge, iff_cond = ev.iff_condition,
                       ctx_ptr, proc]() mutable {
        if (proc && !proc->active) return true;
        return HandleEdgeEvent(h, var, edge, iff_cond, *ctx_ptr);
      });
    }
  }

  void await_resume() const noexcept {}

  static bool CheckEdge(const Variable* var, Edge edge) {
    if (edge == Edge::kNone) {
      const auto& prev = var->prev_value;
      const auto& cur = var->value;
      if (prev.nwords != cur.nwords) return true;
      for (uint32_t i = 0; i < prev.nwords; ++i) {
        if (prev.words[i].aval != cur.words[i].aval ||
            prev.words[i].bval != cur.words[i].bval)
          return true;
      }
      return false;
    }
    // Edge events: Table 9-2, detected only on the LSB.
    uint64_t pa = 0, pb = 0, ca = 0, cb = 0;
    if (var->prev_value.nwords > 0) {
      pa = var->prev_value.words[0].aval & 1;
      pb = var->prev_value.words[0].bval & 1;
    }
    if (var->value.nwords > 0) {
      ca = var->value.words[0].aval & 1;
      cb = var->value.words[0].bval & 1;
    }
    bool prev_is_0 = (pa == 0 && pb == 0);
    bool prev_is_1 = (pa == 1 && pb == 0);
    bool prev_is_xz = (pb == 1);
    bool cur_is_0 = (ca == 0 && cb == 0);
    bool cur_is_1 = (ca == 1 && cb == 0);
    bool pos = (prev_is_0 && !cur_is_0) || (prev_is_xz && cur_is_1);
    bool neg = (prev_is_1 && !cur_is_1) || (prev_is_xz && cur_is_0);
    if (edge == Edge::kPosedge) return pos;
    if (edge == Edge::kNegedge) return neg;
    return pos || neg;  // Edge::kEdge
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

// §9.4.2.4: Awaiter for sequence events (@(seq_name)). Blocks the process
// until the sequence reaches its end point (R2), then resumes following the
// Observed region (R3) — i.e. in the Reactive region.  The sequence is
// instantiated as if by assert property (R4); its endpoint fires an internal
// named event that this awaiter watches.
struct SequenceEventAwaiter {
  SimContext& ctx;
  const std::vector<EventExpr>& events;

  bool await_ready() const noexcept { return false; }

  void await_suspend(std::coroutine_handle<> h) {
    for (const auto& ev : events) {
      if (!ev.is_sequence_event || !ev.signal) continue;
      std::string_view seq_name;
      if (ev.signal->kind == ExprKind::kIdentifier)
        seq_name = ev.signal->text;
      else if (ev.signal->kind == ExprKind::kCall)
        seq_name = ev.signal->callee;
      if (seq_name.empty()) continue;

      // Create or find the endpoint event variable for this sequence.
      std::string ep_name = std::string("__seq_") + std::string(seq_name);
      auto* ep_var = ctx.FindVariable(ep_name);
      if (!ep_var) {
        ep_var = ctx.CreateVariable(ep_name, 1);
        ep_var->is_event = true;
      }
      // R3: Resume in the Reactive region (following Observed).
      auto* sched = &ctx.GetScheduler();
      auto* ctx_ptr = &ctx;
      ep_var->AddWatcher([h, sched, ctx_ptr]() mutable {
        auto* event = sched->GetEventPool().Acquire();
        event->callback = [h]() mutable { h.resume(); };
        sched->ScheduleEvent(ctx_ptr->CurrentTime(), Region::kReactive, event);
        return true;
      });
    }
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
    auto* proc = ctx.CurrentProcess();
    for (auto name : var_names) {
      auto* var = ctx.FindVariable(name);
      if (!var) continue;
      var->prev_value = var->value;
      var->AddWatcher([h, proc]() mutable {
        if (proc && !proc->active) return true;
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

// Awaiter for wait fork (§9.6.1). Suspends the parent coroutine until all
// immediate child subprocesses spawned by fork/join_none have terminated.
struct WaitForkAwaiter {
  WaitForkState* state;

  bool await_ready() const noexcept { return state->remaining == 0; }

  void await_suspend(std::coroutine_handle<> h) noexcept { state->waiter = h; }

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

// §9.7: Awaiter for process.await(). Suspends the caller until the
// target process reaches FINISHED or KILLED state.
struct ProcessAwaitAwaiter {
  Process* target;

  bool await_ready() {
    return !target || target->sv_state == ProcessState::kFinished ||
           target->sv_state == ProcessState::kKilled;
  }

  void await_suspend(std::coroutine_handle<> h) {
    target->await_waiters.push_back(h);
  }

  void await_resume() const noexcept {}
};

// §15.3.3: Awaiter for semaphore get(). Suspends the coroutine when
// insufficient keys are available; resumes when Put() adds enough keys.
struct SemaphoreGetAwaiter {
  SemaphoreObject& sem;
  int32_t count;

  bool await_ready() {
    auto status = sem.Get(count);
    return status != SemGetStatus::kBlock;
  }

  void await_suspend(std::coroutine_handle<> h) {
    sem.waiters.push_back({count, h});
  }

  void await_resume() const noexcept {}
};

}  // namespace delta
