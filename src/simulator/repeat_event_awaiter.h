#pragma once

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

struct RepeatEventAwaiter {
  SimContext& ctx;
  const std::vector<EventExpr>& events;
  Arena& arena;
  uint64_t count;

  bool await_ready() const noexcept { return count == 0; }

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

  struct EdgeOperandGate {
    bool passed;
    bool keep_armed_return;
  };

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
    if (spec.iff_cond &&
        !EvalExpr(spec.iff_cond, target.ctx, target.ctx.GetArena())
             .IsTruthy()) {
      var->prev_value.Capture(var->value);
      return {false, false};
    }
    var->prev_value.Capture(var->value);
    return {true, false};
  }

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
