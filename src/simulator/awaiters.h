#pragma once

#include <coroutine>
#include <cstdint>
#include <memory>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "parser/ast.h"
#include "simulator/clocking.h"
#include "simulator/evaluation.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/sync_objects.h"
#include "simulator/variable.h"

namespace delta {

// Resolves a member-access event-control signal down to a Variable*. Tries a
// clocking-block member first, then falls back to a flattened hierarchical
// name lookup. Returns nullptr when neither resolves.
inline Variable* ResolveMemberAccessSignal(const Expr* signal,
                                           SimContext& ctx) {
  Variable* var = nullptr;
  if (signal->lhs && signal->lhs->kind == ExprKind::kIdentifier) {
    auto* mgr = ctx.GetClockingManager();
    std::string_view member;
    if (signal->rhs && signal->rhs->kind == ExprKind::kIdentifier)
      member = signal->rhs->text;
    else if (!signal->text.empty())
      member = signal->text;
    if (mgr && !member.empty())
      var = mgr->ResolveClockingMember(signal->lhs->text, member, ctx);
  }
  if (!var) {
    std::string hier_name;
    BuildLhsName(signal, hier_name);
    var = ctx.FindVariable(hier_name);
  }
  return var;
}

// Resolves an event-control signal expression down to a Variable*. Handles
// plain identifiers, clocking-block member accesses, and hierarchical names.
// Returns nullptr when the expression is not one of these forms (e.g. a
// compound expression) or cannot be resolved.
inline Variable* ResolveSignalToVariable(const Expr* signal, SimContext& ctx) {
  if (signal->kind == ExprKind::kIdentifier) {
    return ctx.FindVariable(signal->text);
  }
  if (signal->kind == ExprKind::kMemberAccess) {
    return ResolveMemberAccessSignal(signal, ctx);
  }
  return nullptr;
}

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

      if (proc && proc->is_suspended) return;
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

struct EventAwaiter {
  SimContext& ctx;
  const std::vector<EventExpr>& events;
  Arena& arena;

  bool await_ready() const noexcept { return false; }

  // Arms a watcher on a named-event variable that resumes the suspended
  // coroutine (respecting active/suspended process state) once when triggered.
  static void AttachEventVarWatcher(Variable* var, std::coroutine_handle<> h,
                                    SimContext& ctx, Process* proc) {
    auto* ctx_ptr = &ctx;
    var->AddWatcher([h, proc, ctx_ptr]() mutable {
      if (proc && !proc->active) return true;

      if (proc && proc->is_suspended) return false;
      ResumeMaybeReactive(h, proc, *ctx_ptr);
      return true;
    });
  }

  // Arms an edge-sensitive watcher on a value-carrying variable, delegating
  // the edge/iff evaluation and resume decision to HandleEdgeEvent.
  static void AttachEdgeVarWatcher(Variable* var, const EventExpr& ev,
                                   std::coroutine_handle<> h, SimContext& ctx,
                                   Process* proc) {
    var->prev_value = var->value;
    auto* ctx_ptr = &ctx;
    var->AddWatcher([h, var, edge = ev.edge, iff_cond = ev.iff_condition,
                     ctx_ptr, proc]() mutable {
      if (proc && !proc->active) return true;

      if (proc && proc->is_suspended) return false;
      return HandleEdgeEvent(h, var, edge, iff_cond, *ctx_ptr, proc);
    });
  }

  void await_suspend(std::coroutine_handle<> h) {
    auto* proc = ctx.CurrentProcess();
    for (const auto& ev : events) {
      if (!ev.signal) continue;
      if (ev.signal->kind != ExprKind::kIdentifier &&
          ev.signal->kind != ExprKind::kMemberAccess) {
        AttachCompoundWatchers(ev, h, proc);
        continue;
      }
      Variable* var = ResolveSignalToVariable(ev.signal, ctx);
      if (!var) continue;
      if (var->is_event) {
        AttachEventVarWatcher(var, h, ctx, proc);
        continue;
      }
      AttachEdgeVarWatcher(var, ev, h, ctx, proc);
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

    return CheckEdgeOnValues(var->prev_value, var->value, edge);
  }

  static bool HandleEdgeEvent(std::coroutine_handle<>& h, Variable* var,
                              Edge edge, const Expr* iff_cond, SimContext& ctx,
                              Process* proc) {
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
    ResumeMaybeReactive(h, proc, ctx);
    return true;
  }

  static void CollectExprIdentifiers(const Expr* e,
                                     std::vector<std::string_view>& out) {
    if (!e) return;
    if (e->kind == ExprKind::kIdentifier) {
      out.push_back(e->text);
      return;
    }
    CollectExprIdentifiers(e->lhs, out);
    CollectExprIdentifiers(e->rhs, out);
    CollectExprIdentifiers(e->condition, out);
    CollectExprIdentifiers(e->true_expr, out);
    CollectExprIdentifiers(e->false_expr, out);
    CollectExprIdentifiers(e->base, out);
    CollectExprIdentifiers(e->index, out);
    CollectExprIdentifiers(e->index_end, out);
    for (auto* a : e->args) CollectExprIdentifiers(a, out);
    for (auto* el : e->elements) CollectExprIdentifiers(el, out);
  }

  static bool Logic4VecBitsEqual(const Logic4Vec& a, const Logic4Vec& b) {
    if (a.nwords != b.nwords) return false;
    for (uint32_t i = 0; i < a.nwords; ++i) {
      if (a.words[i].aval != b.words[i].aval ||
          a.words[i].bval != b.words[i].bval)
        return false;
    }
    return true;
  }

  static bool CheckEdgeOnValues(const Logic4Vec& prev, const Logic4Vec& cur,
                                Edge edge) {
    uint64_t pa = 0, pb = 0, ca = 0, cb = 0;
    if (prev.nwords > 0) {
      pa = prev.words[0].aval & 1;
      pb = prev.words[0].bval & 1;
    }
    if (cur.nwords > 0) {
      ca = cur.words[0].aval & 1;
      cb = cur.words[0].bval & 1;
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
    return pos || neg;
  }

  // Body of a compound-expression operand watcher. Re-evaluates the whole
  // signal expression, applies the change/edge/iff gates against the shared
  // previous value, and on a genuine triggering change marks the shared guard
  // consumed and resumes the process once. Returns the AddWatcher convention
  // (true removes the watcher, false keeps it armed).
  static bool EvalCompoundWatcher(std::coroutine_handle<> h,
                                  const std::shared_ptr<Logic4Vec>& prev,
                                  const std::shared_ptr<bool>& consumed,
                                  const Expr* signal, Edge edge,
                                  const Expr* iff_cond, SimContext& ctx,
                                  Process* proc) {
    if (*consumed) return true;
    if (proc && !proc->active) return true;
    auto cur = EvalExpr(signal, ctx, ctx.GetArena());
    if (Logic4VecBitsEqual(cur, *prev)) {
      return false;
    }
    if (edge != Edge::kNone && !CheckEdgeOnValues(*prev, cur, edge)) {
      *prev = cur;
      return false;
    }
    *prev = cur;
    if (iff_cond) {
      auto val = EvalExpr(iff_cond, ctx, ctx.GetArena());
      if (val.ToUint64() == 0) return false;
    }
    *consumed = true;
    ResumeMaybeReactive(h, proc, ctx);
    return true;
  }

  void AttachCompoundWatchers(const EventExpr& ev, std::coroutine_handle<> h,
                              Process* proc) {
    std::vector<std::string_view> names;
    CollectExprIdentifiers(ev.signal, names);
    if (names.empty()) return;
    auto prev =
        std::make_shared<Logic4Vec>(EvalExpr(ev.signal, ctx, ctx.GetArena()));
    auto consumed = std::make_shared<bool>(false);
    auto* ctx_ptr = &ctx;
    const Expr* signal = ev.signal;
    const Expr* iff_cond = ev.iff_condition;
    Edge edge = ev.edge;
    for (auto name : names) {
      Variable* op_var = ctx.FindVariable(name);
      if (!op_var) continue;
      op_var->AddWatcher(
          [h, prev, consumed, signal, edge, iff_cond, ctx_ptr, proc]() mutable {
            return EvalCompoundWatcher(h, prev, consumed, signal, edge,
                                       iff_cond, *ctx_ptr, proc);
          });
    }
  }

  static void ResumeMaybeReactive(std::coroutine_handle<> h, Process* proc,
                                  SimContext& ctx) {
    if (proc && proc->is_reactive) {
      auto* event = ctx.GetScheduler().GetEventPool().Acquire();
      event->callback = [h, proc, &ctx]() mutable {
        if (!proc->active) return;
        ctx.SetCurrentProcess(proc);
        h.resume();
      };
      ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), Region::kReactive,
                                       event);
      return;
    }

    if (proc && ctx.IsReactiveContext()) {
      auto* event = ctx.GetScheduler().GetEventPool().Acquire();
      event->callback = [h, proc, &ctx]() mutable {
        if (!proc->active) return;
        ctx.SetCurrentProcess(proc);
        h.resume();
      };
      ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), Region::kActive,
                                       event);
      return;
    }
    h.resume();
  }
};

// §9.4.5 intra-assignment repeat event control. A plain event control is
// awaited once, but the repeat form has to accumulate a fixed number of event
// occurrences across the whole OR-list. Each operand keeps a single persistent
// watcher (rather than being re-armed once per occurrence), so two edges in the
// same time step on different operands are each counted, and a shared guard
// resumes the issuing process exactly once when the target count is reached —
// any later sibling watcher that fires afterwards removes itself without
// touching the already-resumed coroutine.
struct RepeatEventAwaiter {
  SimContext& ctx;
  const std::vector<EventExpr>& events;
  Arena& arena;
  uint64_t count;

  bool await_ready() const noexcept { return count == 0; }

  // Arms a persistent watcher on a named-event operand. Each occurrence is
  // forwarded to tally once the active/suspended gates pass.
  template <typename TallyFn>
  static void ArmEventOperand(Variable* var, std::shared_ptr<bool> done,
                              Process* proc, TallyFn tally) {
    var->AddWatcher([proc, done, tally]() mutable {
      if (*done) return true;
      if (proc && !proc->active) return true;
      if (proc && proc->is_suspended) return false;
      return tally();
    });
  }

  // Arms a persistent edge-sensitive watcher on a value-carrying operand,
  // forwarding qualifying edges (after the iff gate) to tally.
  template <typename TallyFn>
  static void ArmEdgeOperand(Variable* var, const EventExpr& ev,
                             std::shared_ptr<bool> done, SimContext& ctx,
                             Process* proc, TallyFn tally) {
    var->prev_value = var->value;
    Edge edge = ev.edge;
    const Expr* iff_cond = ev.iff_condition;
    auto* ctx_ptr = &ctx;
    var->AddWatcher(
        [var, edge, iff_cond, ctx_ptr, proc, done, tally]() mutable {
          if (*done) return true;
          if (proc && !proc->active) return true;
          if (proc && proc->is_suspended) return false;
          if (!EventAwaiter::CheckEdge(var, edge)) {
            var->prev_value = var->value;
            return false;
          }
          if (iff_cond) {
            auto val = EvalExpr(iff_cond, *ctx_ptr, ctx_ptr->GetArena());
            if (val.ToUint64() == 0) {
              var->prev_value = var->value;
              return false;
            }
          }
          var->prev_value = var->value;
          return tally();
        });
  }

  void await_suspend(std::coroutine_handle<> h) {
    auto* proc = ctx.CurrentProcess();
    auto remaining = std::make_shared<uint64_t>(count);
    auto done = std::make_shared<bool>(false);
    auto* ctx_ptr = &ctx;

    // Counts one occurrence and, when the target is reached, resumes the
    // process once. Returning false keeps the watcher armed for the next
    // occurrence; returning true removes it.
    auto tally = [h, proc, ctx_ptr, remaining, done]() {
      if (*remaining > 0) --(*remaining);
      if (*remaining == 0) {
        *done = true;
        EventAwaiter::ResumeMaybeReactive(h, proc, *ctx_ptr);
        return true;
      }
      return false;
    };

    for (const auto& ev : events) {
      if (!ev.signal) continue;
      Variable* var = ResolveSignalToVariable(ev.signal, ctx);
      if (!var) continue;
      if (var->is_event) {
        ArmEventOperand(var, done, proc, tally);
        continue;
      }
      ArmEdgeOperand(var, ev, done, ctx, proc, tally);
    }
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
    var->AddWatcher([h]() mutable {
      h.resume();
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

struct AnyChangeAwaiter {
  SimContext& ctx;
  const std::vector<std::string_view>& var_names;

  bool await_ready() const noexcept { return false; }

  void await_suspend(std::coroutine_handle<> h) {
    auto* proc = ctx.CurrentProcess();
    auto* ctx_ptr = &ctx;
    for (auto name : var_names) {
      auto* var = ctx.FindVariable(name);
      if (!var) continue;
      var->prev_value = var->value;
      var->AddWatcher([h, proc, ctx_ptr]() mutable {
        if (proc && !proc->active) return true;
        EventAwaiter::ResumeMaybeReactive(h, proc, *ctx_ptr);
        return true;
      });
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
