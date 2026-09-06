#pragma once

// The awaiters a suspended process resumes from, one per thing it can wait
// for: DelayAwaiter for a §9.7 delay control, NamedEventAwaiter for a named
// event, SequenceEventAwaiter for a §16.13 sequence event, AnyChangeAwaiter
// for a change on any of several named variables, InertialDelayAwaiter for a
// §28 inertial delay a change can cancel, ForkJoinAwaiter and WaitForkAwaiter
// for §9.3.2 fork-join completion, CycleDelayAwaiter for a §14.11 cycle delay,
// ProcessAwaitAwaiter for another process finishing, SemaphoreGetAwaiter for a
// §15.3 semaphore and MailboxPutAwaiter for a §15.4 mailbox.
//
// The awaiters for a §9.4.2 event control and its §9.4.5 intra-assignment
// repeat form live in src/simulator/awaiters_event_control.h, which this
// header includes, so a translation unit including this one still sees
// EventAwaiter and RepeatEventAwaiter. AnyChangeAwaiter calls
// EventAwaiter::ResumeMaybeReactive from there.

#include <algorithm>
#include <coroutine>
#include <cstdint>
#include <memory>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "parser/ast.h"
#include "simulator/awaiters_event_control.h"
#include "simulator/clocking.h"
#include "simulator/evaluation.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/sync_objects.h"
#include "simulator/variable.h"

namespace delta {

struct DelayAwaiter {
  SimContext& ctx;
  uint64_t delay_ticks;

  bool await_ready() const noexcept { return false; }

  void await_suspend(std::coroutine_handle<> h) {
    auto time = ctx.CurrentTime() + SimTime{delay_ticks};
    auto region = SelectDelayRegion();
    auto* event = ctx.GetScheduler().GetEventPool().Acquire();
    auto* proc = ctx.CurrentProcess();
    event->callback = [h, proc, &ctx = ctx]() mutable {
      if (proc && !proc->active) return;

      // §9.7: this delay has elapsed, but the process is suspended. The wake is
      // one-shot, so dropping it would strand the coroutine's continuation (h
      // is the inner parked frame; Process::coro is an outer frame). Stash h so
      // resume() can replay it, then return.
      if (proc && proc->is_suspended) {
        proc->pending_wake = h;
        return;
      }
      if (proc) ctx.SetCurrentProcess(proc);
      h.resume();
    };
    ctx.GetScheduler().ScheduleEvent(time, region, event);
  }

  Region SelectDelayRegion() const {
    if (delay_ticks != 0) {
      return ctx.IsReactiveContext() ? Region::kReactive : Region::kActive;
    }
    return ctx.IsReactiveContext() ? Region::kReInactive : Region::kInactive;
  }

  void await_resume() const noexcept {}
};

struct NamedEventAwaiter {
  SimContext& ctx;
  std::string_view event_name;

  bool await_ready() const noexcept { return false; }

  void await_suspend(std::coroutine_handle<> h) {
    auto* var = ctx.FindVariable(event_name);
    if (!var) return;
    auto* proc = ctx.CurrentProcess();
    auto* ctx_ptr = &ctx;
    var->AddWatcher([h, proc, ctx_ptr]() mutable {
      // The watcher fires synchronously inside the triggering process's
      // NotifyWatchers; set the current process to the waiter's own for the
      // resume (so the post-resume flush point sees the right process) and
      // restore it afterward (§9.4 / §12.4.2.1).
      auto* saved = ctx_ptr->CurrentProcess();
      if (proc) ctx_ptr->SetCurrentProcess(proc);
      h.resume();
      ctx_ptr->SetCurrentProcess(saved);
      return true;
    });
  }

  void await_resume() const noexcept {}
};

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

      std::string ep_name = std::string("__seq_") + std::string(seq_name);
      auto* ep_var = ctx.FindVariable(ep_name);
      if (!ep_var) {
        ep_var = ctx.CreateVariable(ep_name, 1);
        ep_var->is_event = true;
      }

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

// Drops from `names` every name that designates no object, leaving a process's
// watch list holding only the names a watcher can be armed on.
//
// §9.2.2.2.1 builds an implicit sensitivity list out of "the expansions of the
// longest static prefix of each net or variable identifier or select expression
// that is read", and an expansion is an object of the design, so a name that
// resolves to none of them is not on the list at all. Both awaiters below
// already read it that way when they arm, by skipping such a name; this is
// where the list itself comes to agree, which is what lets the `read_vars`
// emptiness test at each loop that watches one answer the question it asks.
//
// A list left holding those names reads as though there were something to
// watch, so the coroutine suspends on a set of watchers it never armed. Nothing
// can resume it after that: the process is never scheduled again, and whatever
// it drives holds the value of its last evaluation for the rest of the run with
// no report of any kind. #3436 is one instance of that reaching the output.
// Resuming such a suspension immediately is not the alternative, because each
// of those loops evaluates and awaits without advancing time, so a suspension
// that resumes itself spins for ever.
inline void DropUnwatchableNames(SimContext& ctx,
                                 std::vector<std::string_view>& names) {
  auto designates_no_object = [&ctx](std::string_view name) {
    return ctx.FindVariable(name) == nullptr;
  };
  names.erase(std::remove_if(names.begin(), names.end(), designates_no_object),
              names.end());
}

struct AnyChangeAwaiter {
  SimContext& ctx;
  const std::vector<std::string_view>& var_names;
  // Optional guard shared with the awaiting coroutine, true once that coroutine
  // has resumed for good. An ExecTask-based waiter (the wait statement) has its
  // coroutine frame destroyed the instant it resumes to completion, by the
  // awaiting temporary's destructor as control unwinds — so a stranded sibling
  // watcher cannot even call h.done() safely (that would read a freed frame).
  // Such waiters pass `finished`; every stranded watcher then removes itself by
  // value without touching the handle. SimCoroutine waiters (always_comb /
  // continuous assigns) keep their frame alive at final_suspend, so they leave
  // this null and rely on the h.done() check below.
  std::shared_ptr<bool> finished = nullptr;

  bool await_ready() const noexcept { return false; }

  // Arms the change watcher one named variable carries for one suspension.
  // Factored out of await_suspend for the reason
  // EventAwaiter::AttachEventVarWatcher is factored out of its own: the watcher
  // body is three guards deep inside a loop inside a lambda, which
  // readability-function-cognitive-complexity in etc/clang_tidy/src.yml counts
  // against the function holding it.
  //
  // `fin` and `consumed` answer different questions and both are needed. `fin`
  // and h.done() ask whether the frame is still there; `consumed` asks whether
  // this suspension is still the one the frame is waiting at.
  void AttachChangeWatcher(Variable* var, std::coroutine_handle<> h,
                           Process* proc, const std::shared_ptr<bool>& fin,
                           const std::shared_ptr<bool>& consumed) {
    auto* ctx_ptr = &ctx;
    var->prev_value = var->value;
    var->AddWatcher([h, proc, ctx_ptr, fin, consumed]() mutable {
      // A wait/@* re-suspension arms a fresh watcher on every awaited signal,
      // but watchers are cleared only from the signal that actually fired.
      // Watchers stranded on the other signals accumulate; once one of them
      // resumes the coroutine to completion, the rest would resume an
      // already-finished (or freed) frame -> undefined behavior / SEGFAULT.
      // Drop any such watcher: by the shared guard when present (frame may
      // already be freed), otherwise by the still-alive frame's done() flag.
      if (fin) {
        if (*fin) return true;
      } else if (h.done()) {
        return true;
      }
      if (proc && !proc->active) return true;
      // A sibling variable armed by the same suspension already resumed this
      // await, so the coroutine is now suspended somewhere else. Resuming it
      // here would complete whatever await it moved to instead of this one:
      // when that is a delay, the value takes effect at the change time rather
      // than after the delay §28.16 gives it. Retire this stale watcher. The
      // frame is still alive at this point, so done() above cannot tell the two
      // suspension points apart.
      if (*consumed) return true;
      *consumed = true;
      EventAwaiter::ResumeMaybeReactive(h, proc, *ctx_ptr);
      return true;
    });
  }

  void await_suspend(std::coroutine_handle<> h) {
    auto* proc = ctx.CurrentProcess();
    auto fin = finished;
    // Resumes this suspension at most once. Every watcher armed here shares one
    // guard, so the first named variable to change retires the watchers armed
    // on the others. The guard is created per suspension rather than held as a
    // member: a coroutine that re-arms this awaiter after resuming needs a
    // guard that is still clear, and the watchers of the earlier suspension
    // need one that stays set.
    auto consumed = std::make_shared<bool>(false);
    for (auto name : var_names) {
      auto* var = ctx.FindVariable(name);
      if (!var) continue;
      AttachChangeWatcher(var, h, proc, fin, consumed);
    }
  }

  void await_resume() const noexcept {}
};

struct InertialDelayAwaiter {
  SimContext& ctx;
  uint64_t delay_ticks;
  const std::vector<std::string_view>& var_names;
  std::shared_ptr<bool> fired = std::make_shared<bool>(false);
  std::shared_ptr<bool> expired = std::make_shared<bool>(false);

  bool await_ready() const noexcept { return false; }

  // Schedules the timeout event that, if it fires first, marks the delay as
  // expired and resumes the coroutine. The shared `fired` guard ensures the
  // timeout and the cancel watchers race for a single resume.
  void ScheduleTimeoutEvent(std::coroutine_handle<> h, Process* proc) {
    auto time = ctx.CurrentTime() + SimTime{delay_ticks};
    auto* event = ctx.GetScheduler().GetEventPool().Acquire();
    auto f = fired;
    auto e = expired;
    // If an operand change wins the `fired` race first, this timeout becomes a
    // no-op. Tag it with the same guard so the scheduler can drop the orphaned
    // event without advancing time to it (IEEE 1800 §28 inertial delays). When
    // this timeout fires legitimately, `fired` is still false as the scheduler
    // reaches the slot (the callback below sets it), so the event stays live.
    event->superseded = f;
    event->callback = [h, proc, f, e, &ctx = ctx]() mutable {
      if (*f) return;
      *f = true;
      *e = true;
      if (proc && !proc->active) return;
      if (proc) ctx.SetCurrentProcess(proc);
      h.resume();
    };
    ctx.GetScheduler().ScheduleEvent(time, Region::kActive, event);
  }

  // Arms cancel-on-change watchers on every named variable. The first change
  // before the timeout wins the shared `fired` guard and resumes immediately,
  // leaving `expired` false so await_resume reports the inertial cancellation.
  void ArmCancelWatchers(std::coroutine_handle<> h, Process* proc) {
    for (auto name : var_names) {
      auto* var = ctx.FindVariable(name);
      if (!var) continue;
      var->prev_value = var->value;
      auto f2 = fired;
      var->AddWatcher([h, proc, f2]() mutable {
        if (*f2) return true;
        *f2 = true;
        if (proc && !proc->active) return true;
        h.resume();
        return true;
      });
    }
  }

  void await_suspend(std::coroutine_handle<> h) {
    auto* proc = ctx.CurrentProcess();
    ScheduleTimeoutEvent(h, proc);
    ArmCancelWatchers(h, proc);
  }

  bool await_resume() const noexcept { return *expired; }
};

struct ForkJoinState {
  uint32_t remaining = 0;
  std::coroutine_handle<> parent;
  // The thread that issued the fork, captured so the active-process pointer
  // can be restored when the parent resumes. Without this, the parent would
  // re-enter with whichever child finished last as the current thread, and
  // §18.14.2 thread stability of parent-side draws would be broken.
  Process* parent_proc = nullptr;
  bool join_any = false;
  bool resumed = false;
};

struct ForkJoinAwaiter {
  ForkJoinState* state;

  bool await_ready() const noexcept { return state->remaining == 0; }

  void await_suspend(std::coroutine_handle<> h) noexcept { state->parent = h; }

  void await_resume() const noexcept {}
};

struct WaitForkAwaiter {
  WaitForkState* state;

  bool await_ready() const noexcept { return state->remaining == 0; }

  void await_suspend(std::coroutine_handle<> h) noexcept { state->waiter = h; }

  void await_resume() const noexcept {}
};

struct CycleDelayAwaiter {
  SimContext& ctx;
  uint32_t cycles;

  bool await_ready() const noexcept {
    if (cycles != 0) return false;
    // §14.11: ##0 proceeds immediately only when there is no governing
    // clocking block, or when that block's event has already occurred in the
    // current time step.
    auto* mgr = ctx.GetClockingManager();
    if (!mgr) return true;
    auto block_name = mgr->GetDefaultClocking();
    if (block_name.empty()) return true;
    return mgr->ZeroCycleDelayProceeds(block_name, ctx.CurrentTime());
  }

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
    if (cycles == 0) {
      // §14.11: a ##0 whose clocking event has not yet occurred this time step
      // suspends until that event fires, then proceeds. Resume exactly once.
      auto* done = new bool(false);
      mgr->RegisterEdgeCallback(block_name, ctx, ctx.GetScheduler(),
                                [h, done]() mutable {
                                  if (*done) return;
                                  *done = true;
                                  delete done;
                                  h.resume();
                                });
      return;
    }
    auto* counter = new uint32_t(cycles);
    mgr->RegisterEdgeCallback(block_name, ctx, ctx.GetScheduler(),
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

// §15.4: a process that places a message into a full mailbox shall be
// suspended until enough room becomes available in the queue. When there is
// room the message is stored immediately and the process continues without
// suspending (an unbounded mailbox, never being full, never suspends a
// sender). When the mailbox is full the handle is parked on the put-waiter
// queue; the runtime resumes it from WakePutWaiters() once a get/try_get
// frees a slot, at which point the awaiter stores the deferred message.
struct MailboxPutAwaiter {
  MailboxObject& mbx;
  uint64_t msg;
  bool placed = false;

  bool await_ready() {
    placed = mbx.Put(msg) == MbxPutStatus::kPlaced;
    return placed;
  }

  void await_suspend(std::coroutine_handle<> h) {
    mbx.put_waiters.push_back(h);
  }

  // await_resume runs on both the ready and the resumed paths. The message is
  // already stored when it was placed in await_ready; store it now only when
  // the put had blocked and the runtime has since freed room.
  void await_resume() {
    if (!placed) mbx.Put(msg);
  }
};

}  // namespace delta
