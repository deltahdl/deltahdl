#pragma once

// The awaiter a suspended process resumes from for the §9.4.5 intra-assignment
// repeat event control, built on what an event control's operand is made of
// in awaiters_event_control.h.

#include <coroutine>
#include <cstdint>
#include <memory>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/awaiters_event_control.h"
#include "simulator/evaluation.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

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
      var->prev_value.Capture(var->value);
      return {false, false};
    }
    // §9.4.2.3 with §12.4: the guard is true when any bit of it is 1.
    if (spec.iff_cond &&
        !EvalExpr(spec.iff_cond, target.ctx, target.ctx.GetArena())
             .IsTruthy()) {
      var->prev_value.Capture(var->value);
      return {false, false};
    }
    var->prev_value.Capture(var->value);
    return {true, false};
  }

  // The watcher keeps its own baseline, restored into var->prev_value before
  // each judgment and taken again after it, as EventAwaiter's edge watcher
  // does: the shared field is written by every other watcher on the variable,
  // and judged against what another left there, an edge was missed (§9.4.2).
  template <typename TallyFn>
  static void ArmEdgeOperand(Variable* var, const EventExpr& ev,
                             const std::shared_ptr<bool>& done,
                             ResumeTarget target, const TallyFn& tally) {
    Logic4Snapshot prev;
    prev.Capture(var->value);
    Edge edge = ev.edge;
    const Expr* iff_cond = ev.iff_condition;
    auto* ctx_ptr = &target.ctx;
    auto* proc = target.proc;
    var->AddWatcher(
        [var, prev, edge, iff_cond, ctx_ptr, proc, done, tally]() mutable {
          var->prev_value = prev;
          auto gate = EvalEdgeOperandGate(var, EdgeSpec{edge, iff_cond}, done,
                                          ResumeTarget{*ctx_ptr, proc});
          prev.Capture(var->value);
          if (!gate.passed) return gate.keep_armed_return;
          return tally();
        });
  }

  // §9.4.5 with §9.4.2: an operand that names no single variable, a select
  // (`posedge v[0]`) or a compound expression, is the expression's value, read
  // again on a write to any name it reads (EventAwaiter::WatchOperandNames).
  // EventAwaiter::EvalCompoundTrigger judges each change against the operand's
  // own baseline, its guard `fired` cleared after each occurrence so that every
  // one is counted.
  template <typename TallyFn>
  static void ArmCompoundOperand(const EventExpr& ev, ResumeTarget target,
                                 const std::shared_ptr<bool>& done,
                                 const TallyFn& tally) {
    auto prev = std::make_shared<Logic4Snapshot>();
    prev->Capture(EvalExpr(ev.signal, target.ctx, target.ctx.GetArena()));
    auto fired = std::make_shared<bool>(false);
    auto* ctx_ptr = &target.ctx;
    Process* proc = target.proc;
    const Expr* signal = ev.signal;
    const EdgeSpec kSpec{ev.edge, ev.iff_condition};
    EventAwaiter::WatchOperandNames(
        signal, target.ctx,
        [prev, fired, done, tally, signal, kSpec, ctx_ptr, proc]() mutable {
          if (*done) return true;
          const auto kTrigger = EventAwaiter::EvalCompoundTrigger(
              CompoundOperand{prev, fired, signal}, kSpec,
              ResumeTarget{*ctx_ptr, proc});
          if (!kTrigger.resume) return kTrigger.removed;
          *fired = false;
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
      if (!var) {
        ArmCompoundOperand(ev, ResumeTarget{ctx, proc}, done, tally);
        continue;
      }
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
