#include "simulation/lowerer.h"

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaboration/rtlir.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/process.h"
#include "simulation/sim_context.h"
#include "simulation/stmt_exec.h"

namespace delta {

Lowerer::Lowerer(SimContext& ctx, Arena& arena, DiagEngine& diag)
    : ctx_(ctx), arena_(arena), diag_(diag) {}

// --- Coroutine factories ---

static SimCoroutine MakeInitialCoroutine(const Stmt* body, SimContext& ctx,
                                         Arena& arena) {
  ExecStmt(body, ctx, arena);
  co_return;
}

static SimCoroutine MakeAlwaysCombCoroutine(const Stmt* body, SimContext& ctx,
                                            Arena& arena) {
  ExecStmt(body, ctx, arena);
  co_return;
}

static SimCoroutine MakeContAssignCoroutine(const Expr* lhs, const Expr* rhs,
                                            SimContext& ctx, Arena& arena) {
  auto val = EvalExpr(rhs, ctx, arena);
  if (lhs && lhs->kind == ExprKind::kIdentifier) {
    auto* var = ctx.FindVariable(lhs->text);
    if (var) var->value = val;
  }
  co_return;
}

// --- Schedule helper ---

static void ScheduleProcess(Process* proc, Scheduler& sched, Arena& arena) {
  auto* event = arena.Create<Event>();
  event->callback = [proc]() { proc->Resume(); };
  sched.ScheduleEvent(SimTime{0}, Region::kActive, event);
}

// --- Module lowering ---

void Lowerer::LowerModule(const RtlirModule* mod) {
  // Create variables for all declared nets and variables.
  for (const auto& net : mod->nets) {
    ctx_.CreateVariable(net.name, net.width);
  }
  for (const auto& var : mod->variables) {
    ctx_.CreateVariable(var.name, var.width);
  }
  // Create variables for output ports.
  for (const auto& port : mod->ports) {
    if (!ctx_.FindVariable(port.name)) {
      ctx_.CreateVariable(port.name, port.width);
    }
  }

  // Lower processes.
  for (const auto& proc : mod->processes) {
    LowerProcess(proc);
  }

  // Lower continuous assignments.
  for (const auto& ca : mod->assigns) {
    LowerContAssign(ca);
  }
}

// --- Process lowering ---

void Lowerer::LowerProcess(const RtlirProcess& proc) {
  auto* p = arena_.Create<Process>();
  p->id = next_id_++;
  p->home_region = Region::kActive;

  switch (proc.kind) {
    case RtlirProcessKind::kInitial:
      p->kind = ProcessKind::kInitial;
      p->coro = MakeInitialCoroutine(proc.body, ctx_, arena_).Release();
      break;
    case RtlirProcessKind::kAlways:
    case RtlirProcessKind::kAlwaysComb:
    case RtlirProcessKind::kAlwaysLatch:
      p->kind = ProcessKind::kAlwaysComb;
      p->coro = MakeAlwaysCombCoroutine(proc.body, ctx_, arena_).Release();
      break;
    case RtlirProcessKind::kAlwaysFF:
      p->kind = ProcessKind::kAlwaysFF;
      p->coro = MakeAlwaysCombCoroutine(proc.body, ctx_, arena_).Release();
      break;
    case RtlirProcessKind::kFinal:
      p->kind = ProcessKind::kFinal;
      // Final blocks run at simulation end, not at time 0.
      p->coro = MakeInitialCoroutine(proc.body, ctx_, arena_).Release();
      return;  // Don't schedule at time 0.
  }

  ScheduleProcess(p, ctx_.GetScheduler(), arena_);
}

// --- Continuous assignment lowering ---

void Lowerer::LowerContAssign(const RtlirContAssign& ca) {
  auto* p = arena_.Create<Process>();
  p->kind = ProcessKind::kContAssign;
  p->id = next_id_++;
  p->home_region = Region::kActive;
  p->coro = MakeContAssignCoroutine(ca.lhs, ca.rhs, ctx_, arena_).Release();

  ScheduleProcess(p, ctx_.GetScheduler(), arena_);
}

// --- Design lowering ---

void Lowerer::Lower(const RtlirDesign* design) {
  if (!design) return;
  for (auto* mod : design->top_modules) {
    LowerModule(mod);
  }
}

}  // namespace delta
