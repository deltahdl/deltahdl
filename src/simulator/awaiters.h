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

// Parameter-bundle entities for the event-control awaiters below (§9.4.2
// event control, §9.4.5 intra-assignment repeat event control). These mirror
// the real domain objects the watcher helpers operate on, so the helper
// signatures carry one struct per entity instead of a long flat parameter
// list. They are used only by the inline awaiter helpers in this header.

// The edge qualifier and optional iff condition of a single event-control
// operand (§9.4.2). Both come from one EventExpr (ev.edge, ev.iff_condition)
// and always travel together through the edge-gate helpers.
struct EdgeSpec {
  Edge edge;
  const Expr* iff_cond;
};

// The suspended process and its simulation context, i.e. the target to resume
// once a watcher's gates pass. ctx and proc are obtained together from the
// awaiting coroutine and are forwarded as a pair to every resume decision.
struct ResumeTarget {
  SimContext& ctx;
  Process* proc;
};

// The shared per-operand watch state for a compound (non-identifier) event
// expression operand: the previous evaluated value, the once-only consumed
// guard shared across sibling operand watchers, and the signal expression to
// re-evaluate. One object describes a single compound operand being watched.
struct CompoundOperand {
  const std::shared_ptr<Logic4Vec>& prev;
  const std::shared_ptr<bool>& consumed;
  const Expr* signal;
};

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

struct EventAwaiter {
  SimContext& ctx;
  const std::vector<EventExpr>& events;
  Arena& arena;

  bool await_ready() const noexcept { return false; }

  // Arms a watcher on a named-event variable that resumes the suspended
  // coroutine (respecting active/suspended process state) once when triggered.
  static void AttachEventVarWatcher(Variable* var, std::coroutine_handle<> h,
                                    SimContext& ctx, Process* proc,
                                    const std::shared_ptr<bool>& consumed) {
    auto* ctx_ptr = &ctx;
    var->AddWatcher([h, proc, ctx_ptr, consumed]() mutable {
      if (proc && !proc->active) return true;
      // A sibling operand of the same event control already resumed this
      // await; the coroutine has moved on, so retire this stale watcher.
      if (*consumed) return true;
      if (proc && proc->is_suspended) return false;
      *consumed = true;
      ResumeMaybeReactive(h, proc, *ctx_ptr);
      return true;
    });
  }

  // Arms an edge-sensitive watcher on a value-carrying variable, delegating
  // the edge/iff evaluation and resume decision to HandleEdgeEvent.
  static void AttachEdgeVarWatcher(Variable* var, const EventExpr& ev,
                                   std::coroutine_handle<> h,
                                   ResumeTarget target,
                                   const std::shared_ptr<bool>& consumed) {
    auto* ctx_ptr = &target.ctx;
    auto* proc = target.proc;
    // Per-watcher snapshot of the value as of arming. The single shared
    // var->prev_value is clobbered when one of several coroutines waiting on
    // the same signal's edge resumes and re-arms synchronously mid-notify,
    // which starves every later watcher in that drain (e.g. only the first of
    // two `always @(posedge clk)` blocks would ever fire). Each watcher keeps
    // its own baseline and restores it before delegating to the shared edge
    // logic, so the detections stay independent.
    Logic4Vec prev = var->value;
    var->AddWatcher([h, var, prev, edge = ev.edge, iff_cond = ev.iff_condition,
                     ctx_ptr, proc, consumed]() mutable {
      if (proc && !proc->active) return true;
      // Another operand of the same `@(a or b)` event control already resumed
      // this await; retire this stale sibling so it cannot re-fire the handle.
      if (*consumed) return true;
      if (proc && proc->is_suspended) return false;
      var->prev_value = prev;
      bool fired = HandleEdgeEvent(h, var, EdgeSpec{edge, iff_cond},
                                   ResumeTarget{*ctx_ptr, proc});
      prev = var->value;
      if (fired) *consumed = true;
      return fired;
    });
  }

  void await_suspend(std::coroutine_handle<> h) {
    auto* proc = ctx.CurrentProcess();
    // §9.4.2: an `@(a or b ...)` event control resumes its process at most once
    // per trigger. All operand watchers armed by this await share one guard so
    // that the first to fire retires the rest, even when several operands name
    // the same signal (e.g. `posedge clk or negedge clk`).
    auto consumed = std::make_shared<bool>(false);
    for (const auto& ev : events) {
      if (!ev.signal) continue;
      if (ev.signal->kind != ExprKind::kIdentifier &&
          ev.signal->kind != ExprKind::kMemberAccess) {
        AttachCompoundWatchers(ev, h, proc, consumed);
        continue;
      }
      Variable* var = ResolveSignalToVariable(ev.signal, ctx);
      if (!var) continue;
      if (var->is_event) {
        AttachEventVarWatcher(var, h, ctx, proc, consumed);
        continue;
      }
      AttachEdgeVarWatcher(var, ev, h, ResumeTarget{ctx, proc}, consumed);
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

  // Evaluates the edge gate for an edge-sensitive variable watcher. On a
  // qualifying edge returns true; otherwise resyncs prev_value and returns
  // false so the watcher stays armed without resuming.
  static bool EdgeGatePasses(Variable* var, Edge edge) {
    if (CheckEdge(var, edge)) return true;
    var->prev_value = var->value;
    return false;
  }

  // Evaluates the optional iff condition for an edge-sensitive variable
  // watcher. Returns true when there is no condition or it is non-zero;
  // otherwise resyncs prev_value and returns false.
  static bool IffGatePasses(Variable* var, const Expr* iff_cond,
                            SimContext& ctx) {
    if (!iff_cond) return true;
    auto val = EvalExpr(iff_cond, ctx, ctx.GetArena());
    if (val.ToUint64() != 0) return true;
    var->prev_value = var->value;
    return false;
  }

  static bool HandleEdgeEvent(std::coroutine_handle<>& h, Variable* var,
                              const EdgeSpec& spec, ResumeTarget target) {
    if (!EdgeGatePasses(var, spec.edge)) return false;
    if (!IffGatePasses(var, spec.iff_cond, target.ctx)) return false;
    ResumeMaybeReactive(h, target.proc, target.ctx, spec.edge == Edge::kNone);
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
  // Result of a compound-watcher trigger evaluation. `removed` carries the
  // AddWatcher return value to use when the watcher is not resuming;
  // `resume` is set only when every gate passed and the process should run.
  struct CompoundTrigger {
    bool removed;
    bool resume;
  };

  // Applies the change/edge/iff gates for a compound-expression operand
  // watcher against the shared previous value, updating *prev in place. The
  // shared `consumed` guard ensures the resume happens at most once across all
  // sibling watchers. Does not perform the resume itself.
  static CompoundTrigger EvalCompoundTrigger(const CompoundOperand& op,
                                             const EdgeSpec& spec,
                                             ResumeTarget target) {
    if (*op.consumed) return {true, false};
    if (target.proc && !target.proc->active) return {true, false};
    auto cur = EvalExpr(op.signal, target.ctx, target.ctx.GetArena());
    if (Logic4VecBitsEqual(cur, *op.prev)) return {false, false};
    if (spec.edge != Edge::kNone &&
        !CheckEdgeOnValues(*op.prev, cur, spec.edge)) {
      *op.prev = cur;
      return {false, false};
    }
    *op.prev = cur;
    if (spec.iff_cond) {
      auto val = EvalExpr(spec.iff_cond, target.ctx, target.ctx.GetArena());
      if (val.ToUint64() == 0) return {false, false};
    }
    *op.consumed = true;
    return {true, true};
  }

  static bool EvalCompoundWatcher(std::coroutine_handle<> h,
                                  const CompoundOperand& op,
                                  const EdgeSpec& spec, ResumeTarget target) {
    auto trigger = EvalCompoundTrigger(op, spec, target);
    if (!trigger.resume) return trigger.removed;
    ResumeMaybeReactive(h, target.proc, target.ctx, spec.edge == Edge::kNone);
    return true;
  }

  void AttachCompoundWatchers(const EventExpr& ev, std::coroutine_handle<> h,
                              Process* proc,
                              const std::shared_ptr<bool>& consumed) {
    std::vector<std::string_view> names;
    CollectExprIdentifiers(ev.signal, names);
    if (names.empty()) return;
    auto prev =
        std::make_shared<Logic4Vec>(EvalExpr(ev.signal, ctx, ctx.GetArena()));
    auto* ctx_ptr = &ctx;
    const Expr* signal = ev.signal;
    const Expr* iff_cond = ev.iff_condition;
    Edge edge = ev.edge;
    for (auto name : names) {
      Variable* op_var = ctx.FindVariable(name);
      if (!op_var) continue;
      op_var->AddWatcher([h, prev, consumed, signal, edge, iff_cond, ctx_ptr,
                          proc]() mutable {
        return EvalCompoundWatcher(h, CompoundOperand{prev, consumed, signal},
                                   EdgeSpec{edge, iff_cond},
                                   ResumeTarget{*ctx_ptr, proc});
      });
    }
  }

  static void ResumeMaybeReactive(std::coroutine_handle<> h, Process* proc,
                                  SimContext& ctx, bool defer = false) {
    // §9.2.2.2 / §4: a level-sensitive (non-edge) process triggered by another
    // process's blocking write must observe *settled* inputs, so its evaluation
    // is scheduled into the Active region rather than resumed synchronously in
    // the middle of the writer's NotifyWatchers loop. Otherwise an always @*
    // reading two signals that the writer sets in sequence (a=..; b=..) would
    // fire on the first write and read the second signal before it is updated.
    // Edge-sensitive (posedge/negedge) resumes stay synchronous.
    if (defer && proc && !proc->is_reactive && !ctx.IsReactiveContext()) {
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
    // §9.4: the coroutine being resumed belongs to `proc`. A synchronous resume
    // runs inside whatever process is currently executing (e.g. the one that
    // drove the awaited signal in NotifyWatchers), so set the current process
    // to `proc` for the duration of the resume and restore it afterward; this
    // keeps per-process state (FlushPendingViolations, name lookup) correct
    // without disturbing the caller's NotifyWatchers loop.
    if (proc) {
      auto* saved = ctx.CurrentProcess();
      ctx.SetCurrentProcess(proc);
      h.resume();
      ctx.SetCurrentProcess(saved);
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
  static void ArmEventOperand(Variable* var, const std::shared_ptr<bool>& done,
                              Process* proc, const TallyFn& tally) {
    var->AddWatcher([proc, done, tally]() mutable {
      if (*done) return true;
      if (proc && !proc->active) return true;
      if (proc && proc->is_suspended) return false;
      return tally();
    });
  }

  // Arms a persistent edge-sensitive watcher on a value-carrying operand,
  // forwarding qualifying edges (after the iff gate) to tally.
  // Edge-watcher gate result. `passed` is true when a qualifying edge (and the
  // iff condition) was seen and the occurrence should be tallied; otherwise
  // `keep_armed_return` carries the AddWatcher value to return.
  struct EdgeOperandGate {
    bool passed;
    bool keep_armed_return;
  };

  // Applies the active/suspended/edge/iff gates for a repeat edge operand
  // watcher, resyncing var->prev_value on each non-tally exit. Returns whether
  // the occurrence should be tallied along with the watcher return value to use
  // when it should not.
  static EdgeOperandGate EvalEdgeOperandGate(Variable* var,
                                             const EdgeSpec& spec,
                                             const std::shared_ptr<bool>& done,
                                             ResumeTarget target) {
    if (*done) return {false, true};
    if (target.proc && !target.proc->active) return {false, true};
    if (target.proc && target.proc->is_suspended) return {false, false};
    if (!EventAwaiter::CheckEdge(var, spec.edge)) {
      var->prev_value = var->value;
      return {false, false};
    }
    if (spec.iff_cond) {
      auto val = EvalExpr(spec.iff_cond, target.ctx, target.ctx.GetArena());
      if (val.ToUint64() == 0) {
        var->prev_value = var->value;
        return {false, false};
      }
    }
    var->prev_value = var->value;
    return {true, false};
  }

  template <typename TallyFn>
  static void ArmEdgeOperand(Variable* var, const EventExpr& ev,
                             const std::shared_ptr<bool>& done,
                             ResumeTarget target, const TallyFn& tally) {
    var->prev_value = var->value;
    Edge edge = ev.edge;
    const Expr* iff_cond = ev.iff_condition;
    auto* ctx_ptr = &target.ctx;
    auto* proc = target.proc;
    var->AddWatcher(
        [var, edge, iff_cond, ctx_ptr, proc, done, tally]() mutable {
          auto gate = EvalEdgeOperandGate(var, EdgeSpec{edge, iff_cond}, done,
                                          ResumeTarget{*ctx_ptr, proc});
          if (!gate.passed) return gate.keep_armed_return;
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
      ArmEdgeOperand(var, ev, done, ResumeTarget{ctx, proc}, tally);
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

  void await_suspend(std::coroutine_handle<> h) {
    auto* proc = ctx.CurrentProcess();
    auto* ctx_ptr = &ctx;
    auto fin = finished;
    for (auto name : var_names) {
      auto* var = ctx.FindVariable(name);
      if (!var) continue;
      var->prev_value = var->value;
      var->AddWatcher([h, proc, ctx_ptr, fin]() mutable {
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
