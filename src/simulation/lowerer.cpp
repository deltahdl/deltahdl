#include "simulation/lowerer.h"

#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaboration/rtlir.h"
#include "elaboration/sensitivity.h"
#include "parser/ast.h"
#include "simulation/awaiters.h"
#include "simulation/eval.h"
#include "simulation/net.h"
#include "simulation/process.h"
#include "simulation/sim_context.h"
#include "simulation/stmt_exec.h"

namespace delta {

Lowerer::Lowerer(SimContext& ctx, Arena& arena, DiagEngine& diag)
    : ctx_(ctx), arena_(arena), diag_(diag) {}

// --- Coroutine factories ---

static SimCoroutine MakeInitialCoroutine(const Stmt* body, SimContext& ctx,
                                         Arena& arena) {
  co_await ExecStmt(body, ctx, arena);
}

static SimCoroutine MakeAlwaysCoroutine(const Stmt* body, SimContext& ctx,
                                        Arena& arena) {
  while (!ctx.StopRequested()) {
    auto result = co_await ExecStmt(body, ctx, arena);
    if (result != StmtResult::kDone) break;
  }
}

static SimCoroutine MakeAlwaysSensCoroutine(const Stmt* body,
                                            const std::vector<EventExpr>& sens,
                                            SimContext& ctx, Arena& arena) {
  while (!ctx.StopRequested()) {
    co_await EventAwaiter{ctx, sens};
    auto result = co_await ExecStmt(body, ctx, arena);
    if (result != StmtResult::kDone) break;
  }
}

static SimCoroutine MakeAlwaysCombCoroutine(const Stmt* body, SimContext& ctx,
                                            Arena& arena) {
  auto read_vars = CollectReadSignals(body);
  while (!ctx.StopRequested()) {
    co_await ExecStmt(body, ctx, arena);
    if (read_vars.empty()) break;
    co_await AnyChangeAwaiter{ctx, read_vars};
  }
}

static SimCoroutine MakeContAssignCoroutine(const Expr* lhs, const Expr* rhs,
                                            SimContext& ctx, Arena& arena) {
  auto val = EvalExpr(rhs, ctx, arena);
  if (lhs && lhs->kind == ExprKind::kIdentifier) {
    auto* var = ctx.FindVariable(lhs->text);
    if (var) {
      var->value = val;
      var->NotifyWatchers();
    }
  }
  co_return;
}

// --- Schedule helper ---

static void ScheduleProcess(Process* proc, Scheduler& sched) {
  auto* event = sched.GetEventPool().Acquire();
  event->callback = [proc]() { proc->Resume(); };
  sched.ScheduleEvent(SimTime{0}, Region::kActive, event);
}

// --- Module lowering ---

void Lowerer::LowerModule(const RtlirModule* mod) {
  // Create Net objects for all declared nets (with resolution support).
  for (const auto& net : mod->nets) {
    ctx_.CreateNet(net.name, net.net_type, net.width);
  }
  // Create variables for all declared variables.
  for (const auto& var : mod->variables) {
    auto* v = ctx_.CreateVariable(var.name, var.width);
    if (var.is_event) v->is_event = true;
    if (var.is_string) ctx_.RegisterStringVariable(var.name);
  }
  // Create variables for output ports.
  for (const auto& port : mod->ports) {
    if (!ctx_.FindVariable(port.name)) {
      ctx_.CreateVariable(port.name, port.width);
    }
  }

  // Register function declarations.
  for (auto* func : mod->function_decls) {
    ctx_.RegisterFunction(func->name, func);
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

static void RegisterSensitivity(const RtlirProcess& proc, Process* p,
                                SimContext& ctx) {
  auto signals = CollectReadSignals(proc.body);
  for (auto name : signals) {
    ctx.AddSensitivity(name, p);
  }
}

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
      p->kind = ProcessKind::kAlways;
      if (!proc.sensitivity.empty()) {
        p->coro =
            MakeAlwaysSensCoroutine(proc.body, proc.sensitivity, ctx_, arena_)
                .Release();
      } else {
        p->coro = MakeAlwaysCoroutine(proc.body, ctx_, arena_).Release();
      }
      break;
    case RtlirProcessKind::kAlwaysComb:
    case RtlirProcessKind::kAlwaysLatch:
      p->kind = ProcessKind::kAlwaysComb;
      p->coro = MakeAlwaysCombCoroutine(proc.body, ctx_, arena_).Release();
      RegisterSensitivity(proc, p, ctx_);
      break;
    case RtlirProcessKind::kAlwaysFF:
      p->kind = ProcessKind::kAlwaysFF;
      p->coro = MakeAlwaysCombCoroutine(proc.body, ctx_, arena_).Release();
      break;
    case RtlirProcessKind::kFinal:
      p->kind = ProcessKind::kFinal;
      p->coro = MakeInitialCoroutine(proc.body, ctx_, arena_).Release();
      ctx_.RegisterFinalProcess(p);
      return;  // Don't schedule at time 0.
  }

  ScheduleProcess(p, ctx_.GetScheduler());
}

// --- Continuous assignment lowering ---

void Lowerer::LowerContAssign(const RtlirContAssign& ca) {
  auto* p = arena_.Create<Process>();
  p->kind = ProcessKind::kContAssign;
  p->id = next_id_++;
  p->home_region = Region::kActive;
  p->coro = MakeContAssignCoroutine(ca.lhs, ca.rhs, ctx_, arena_).Release();

  ScheduleProcess(p, ctx_.GetScheduler());
}

// --- Design lowering ---

void Lowerer::Lower(const RtlirDesign* design) {
  if (!design) return;
  for (auto* mod : design->top_modules) {
    LowerModule(mod);
  }
}

}  // namespace delta
