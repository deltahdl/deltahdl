#include <coroutine>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/awaiters_event_control.h"
#include "simulator/eval_function_internal.h"
#include "simulator/lowerer.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine_sampling.h"

namespace delta {

namespace {

// Resumes the process in the Pre-Observed region of the time step it
// suspends in, where §17.7.2 has the free checker variables solved: after
// every Active-set change and before the Observed region checks the
// assumptions and assertions reading them.
struct PreObservedAwaiter {
  SimContext& ctx;

  bool await_ready() const noexcept { return false; }

  void await_suspend(std::coroutine_handle<> h) {
    auto* event = ctx.GetScheduler().GetEventPool().Acquire();
    auto* proc = ctx.CurrentProcess();
    event->callback = [h, proc, &ctx = ctx]() {
      ctx.SetCurrentProcess(proc);
      h.resume();
    };
    ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), Region::kPreObserved,
                                     event);
  }

  void await_resume() const noexcept {}
};

// At each clocking event of the assume set, the free variables take values
// satisfying its assumptions, drawn by the scope randomize `solve` whose
// arguments they are and whose inline constraints the assumptions are.
SimCoroutine MakeFreeVariableSolverCoroutine(const Expr* solve,
                                             std::vector<EventExpr> clock,
                                             SimContext& ctx, Arena& arena) {
  while (!ctx.StopRequested()) {
    co_await EventAwaiter{ctx, clock, arena};
    co_await PreObservedAwaiter{ctx};
    Logic4Vec drawn;
    TryEvalScopeRandomizeCall(solve, ctx, arena, drawn);
  }
}

// §17.7.2: an assumption of the assume set whose property is a boolean, the
// form a draw can satisfy at one clocking event.
bool IsBooleanAssumption(const RtlirProcess& proc) {
  const Stmt* body = proc.body;
  return proc.is_concurrent_clocked && body != nullptr &&
         body->kind == StmtKind::kAssumeImmediate &&
         body->assert_expr != nullptr && body->assert_property == nullptr &&
         body->assert_sequence == nullptr;
}

Expr* NameExpr(std::string_view name, Arena& arena) {
  auto* id = arena.Create<Expr>();
  id->kind = ExprKind::kIdentifier;
  id->text = name;
  return id;
}

}  // namespace

// §17.7.2: the free variables of a checker instance are assigned, at each
// clocking event of its assume set, values satisfying the assumptions, found
// by §18.12's scope randomize over them with the assumptions' conditions as
// its constraints; the other variables the conditions read stand at their
// values. A free variable is read at its current value, which §17.7.2 makes
// its sampled value, so it is kept out of the sampling store. The assume set
// is taken to be on the clock of its first assumption.
void Lowerer::LowerFreeVariableSolver(const RtlirModule* mod) {
  auto* constraints = arena_.Create<ClassMember>();
  const std::vector<EventExpr>* clock = nullptr;
  for (const RtlirProcess& proc : mod->processes) {
    if (!IsBooleanAssumption(proc)) continue;
    constraints->constraint_exprs.push_back(proc.body->assert_expr);
    clock = &proc.sensitivity;
  }
  if (mod->free_variables.empty() || clock == nullptr) return;
  auto* solve = arena_.Create<Expr>();
  solve->kind = ExprKind::kCall;
  solve->lhs = NameExpr("randomize", arena_);
  solve->inline_constraint = constraints;
  for (std::string_view name : mod->free_variables) {
    solve->args.push_back(NameExpr(name, arena_));
    ctx_.AssertionSamples().ExcludeFromSampling(ctx_.FindVariable(name));
  }
  auto* p = arena_.Create<Process>();
  p->kind = ProcessKind::kAlways;
  p->id = next_id_++;
  p->home_region = Region::kActive;
  p->inst_prefix = inst_prefix_;
  p->rng_seed = ctx_.DrawSeedForChild();
  p->coro =
      MakeFreeVariableSolverCoroutine(solve, *clock, ctx_, arena_).Release();
  ScheduleProcess(p, ctx_);
}

}  // namespace delta
