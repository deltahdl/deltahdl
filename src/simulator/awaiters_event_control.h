#pragma once

// The awaiters a suspended process resumes from for a §9.4.2 event control and
// for the §9.4.5 intra-assignment repeat form of it. EventAwaiter arms one
// watcher per operand of an `@(a or b)` list and resumes the coroutine at most
// once per trigger; RepeatEventAwaiter arms a persistent watcher per operand
// and counts occurrences across the whole list until the repeat count is
// reached. The two are here together because they share what an operand is
// made of: ResolveSignalToVariable resolves an operand expression to a
// Variable, EventAwaiter::CheckEdge decides whether an edge qualifies, and
// EventAwaiter::ResumeMaybeReactive decides which region the resume runs in.
// EdgeSpec, ResumeTarget and CompoundOperand are the parameter bundles those
// helpers take.
//
// Split out of src/simulator/awaiters.h, which includes this header and holds
// the awaiters for the other things a process waits on: a delay, a named
// event, a sequence event, a change on any of several variables, an inertial
// delay a change can cancel, a fork join, a cycle delay, a process, a
// semaphore and a mailbox.

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
    // §23.6: a leading `$root` makes the name absolute from the top of the
    // instantiated design, and the parser keeps it in Expr::scope_prefix
    // rather than in the identifier's text (Parser::MakeSysScopePrefix in
    // src/parser/expr_parser_calls.cpp). Reading the text alone drops it and
    // resolves the name in whichever instance is running, so the whole name is
    // spelled out here. BuildLhsName writes both fields, and the member-access
    // branch below already reaches SimContext::FindVariable through it.
    //
    // Only `$root` is spelled out. Expr::scope_prefix also carries the §23.7.1
    // package and `$unit` scope resolution prefixes, which are separated by ::
    // rather than by the period BuildLhsName writes and are not hierarchical
    // names at all.
    if (signal->scope_prefix == "$root") {
      std::string rooted_name;
      BuildLhsName(signal, rooted_name);
      return ctx.FindVariable(rooted_name);
    }
    return ctx.FindVariable(signal->text);
  }
  if (signal->kind == ExprKind::kMemberAccess) {
    return ResolveMemberAccessSignal(signal, ctx);
  }
  return nullptr;
}

struct EventAwaiter {
  SimContext& ctx;
  const std::vector<EventExpr>& events;
  Arena& arena;

  bool await_ready() const noexcept { return false; }

  // Arms a watcher on a named-event variable that resumes the suspended
  // coroutine (respecting active/suspended process state) once when triggered.
  //
  // §9.4.2.3: an `iff` qualifier on the operand gates that resume, so a trigger
  // arriving while the condition is false leaves the process suspended and the
  // watcher armed for the next one.
  static void AttachEventVarWatcher(Variable* var, const Expr* iff_cond,
                                    std::coroutine_handle<> h,
                                    ResumeTarget target,
                                    const std::shared_ptr<bool>& consumed) {
    auto* ctx_ptr = &target.ctx;
    auto* proc = target.proc;
    var->AddWatcher([h, iff_cond, proc, ctx_ptr, consumed]() mutable {
      if (proc && !proc->active) return true;
      // A sibling operand of the same event control already resumed this
      // await; the coroutine has moved on, so retire this stale watcher.
      if (*consumed) return true;
      if (proc && proc->is_suspended) return false;
      if (iff_cond &&
          !EvalExpr(iff_cond, *ctx_ptr, ctx_ptr->GetArena()).IsTruthy())
        return false;
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
        AttachEventVarWatcher(var, ev.iff_condition, h, ResumeTarget{ctx, proc},
                              consumed);
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

  // §9.4.2.3: evaluates the optional iff condition for an edge-sensitive
  // variable watcher. Returns true when there is no condition or the condition
  // is true; otherwise resyncs prev_value and returns false. §12.4 decides what
  // true means, so a condition is true when any of its bits is 1 and false when
  // it is zero, x or z. Logic4Vec::IsTruthy answers that over the whole value,
  // where ToUint64 reads the low 64 bits and would call a wider condition false
  // whenever every bit it set sits above them.
  static bool IffGatePasses(Variable* var, const Expr* iff_cond,
                            SimContext& ctx) {
    if (!iff_cond) return true;
    if (EvalExpr(iff_cond, ctx, ctx.GetArena()).IsTruthy()) return true;
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
    // §9.4.2.3 with §12.4: the guard is true when any bit of it is 1.
    if (spec.iff_cond &&
        !EvalExpr(spec.iff_cond, target.ctx, target.ctx.GetArena()).IsTruthy())
      return {false, false};
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

  // Schedule `h` to resume in `region` at the current time, bound to `proc`.
  // Used by the deferred/reactive branches of ResumeMaybeReactive so the
  // coroutine runs in its own scheduling slot rather than synchronously inside
  // the caller's NotifyWatchers loop.
  static void ScheduleResume(std::coroutine_handle<> h, Process* proc,
                             SimContext& ctx, Region region) {
    auto* event = ctx.GetScheduler().GetEventPool().Acquire();
    event->callback = [h, proc, &ctx]() mutable {
      if (!proc->active) return;
      ctx.SetCurrentProcess(proc);
      h.resume();
    };
    ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), region, event);
  }

  static void ResumeMaybeReactive(std::coroutine_handle<> h, Process* proc,
                                  SimContext& ctx, bool defer = false) {
    // §16.5: "Concurrent assertions are evaluated in the Observed region." A
    // process carrying one is therefore resumed into that region whatever edge
    // its clocking event names, rather than synchronously inside the process
    // that assigned the clock, where `cond = 1; clk = 1;` and
    // `clk = 1; cond = 1;` would reach two different verdicts.
    if (proc && proc->is_concurrent_clocked) {
      ScheduleResume(h, proc, ctx, Region::kObserved);
      return;
    }
    // §9.2.2.2 / §4: a level-sensitive (non-edge) process triggered by another
    // process's blocking write must observe *settled* inputs, so its evaluation
    // is scheduled into the Active region rather than resumed synchronously in
    // the middle of the writer's NotifyWatchers loop. Otherwise an always @*
    // reading two signals that the writer sets in sequence (a=..; b=..) would
    // fire on the first write and read the second signal before it is updated.
    // Edge-sensitive (posedge/negedge) resumes stay synchronous.
    if (defer && proc && !proc->is_reactive && !ctx.IsReactiveContext()) {
      ScheduleResume(h, proc, ctx, Region::kActive);
      return;
    }
    if (proc && proc->is_reactive) {
      ScheduleResume(h, proc, ctx, Region::kReactive);
      return;
    }

    if (proc && ctx.IsReactiveContext()) {
      ScheduleResume(h, proc, ctx, Region::kActive);
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
  // forwarded to tally once the active/suspended gates pass, and §9.4.2.3's
  // `iff` qualifier gates it as it gates an edge operand: an occurrence
  // arriving while the condition is false is not one of the occurrences the
  // repeat is counting.
  template <typename TallyFn>
  static void ArmEventOperand(Variable* var, const Expr* iff_cond,
                              ResumeTarget target,
                              const std::shared_ptr<bool>& done,
                              const TallyFn& tally) {
    auto* ctx_ptr = &target.ctx;
    auto* proc = target.proc;
    var->AddWatcher([iff_cond, ctx_ptr, proc, done, tally]() mutable {
      if (*done) return true;
      if (proc && !proc->active) return true;
      if (proc && proc->is_suspended) return false;
      if (iff_cond &&
          !EvalExpr(iff_cond, *ctx_ptr, ctx_ptr->GetArena()).IsTruthy())
        return false;
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
    // §9.4.2.3 with §12.4: the guard is true when any bit of it is 1.
    if (spec.iff_cond &&
        !EvalExpr(spec.iff_cond, target.ctx, target.ctx.GetArena())
             .IsTruthy()) {
      var->prev_value = var->value;
      return {false, false};
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
        ArmEventOperand(var, ev.iff_condition, ResumeTarget{ctx, proc}, done,
                        tally);
        continue;
      }
      ArmEdgeOperand(var, ev, done, ResumeTarget{ctx, proc}, tally);
    }
  }

  void await_resume() const noexcept {}
};

}  // namespace delta
