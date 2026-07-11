#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "parser/ast.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"

namespace delta {

bool TryEvalProcessStaticCall(const Expr* expr, SimContext& ctx, Arena& arena,
                              Logic4Vec& out) {
  if (!expr->lhs || expr->lhs->kind != ExprKind::kMemberAccess) return false;
  auto* access = expr->lhs;
  if (!access->lhs || access->lhs->kind != ExprKind::kIdentifier) return false;
  if (access->lhs->text != "process") return false;
  if (!access->rhs || access->rhs->kind != ExprKind::kIdentifier) return false;
  if (access->rhs->text != "self") return false;
  auto* proc = ctx.CurrentProcess();
  if (!proc) {
    out = MakeLogic4VecVal(arena, 64, 0);
    return true;
  }
  uint64_t handle = ctx.RegisterProcessHandle(proc);
  out = MakeLogic4VecVal(arena, 64, handle);
  return true;
}

static bool IsRestrictedTarget(const Process* proc) {
  if (!proc) return false;
  return proc->kind == ProcessKind::kFinal ||
         proc->kind == ProcessKind::kContAssign;
}

static bool IsProcessKillable(const Process* proc) {
  return proc && proc->sv_state != ProcessState::kFinished &&
         proc->sv_state != ProcessState::kKilled;
}

static void KillProcessDescendants(Process* proc) {
  std::vector<Process*> stack(proc->children.begin(), proc->children.end());
  while (!stack.empty()) {
    auto* child = stack.back();
    stack.pop_back();
    if (IsProcessKillable(child)) {
      child->active = false;
      child->sv_state = ProcessState::kKilled;
      for (auto* gc : child->children) stack.push_back(gc);
    }
  }
}

static void EvalProcessKill(Process* proc, SimContext& ctx, Arena& arena,
                            Logic4Vec& out) {
  if (IsRestrictedTarget(proc)) {
    ctx.GetDiag().Error(
        {},
        "kill() shall only target a process created by an initial "
        "procedure, always procedure, or fork block");
    out = MakeLogic4VecVal(arena, 1, 0);
    return;
  }
  if (IsProcessKillable(proc)) {
    proc->active = false;
    proc->sv_state = ProcessState::kKilled;
    KillProcessDescendants(proc);
    for (auto& w : proc->await_waiters) {
      if (w) w.resume();
    }
    proc->await_waiters.clear();
  } else if (proc) {
    // §9.7: killing a process that is already FINISHED or KILLED leaves its own
    // state untouched but still forcibly terminates any descendant subprocess
    // that has not yet finished or been killed.
    KillProcessDescendants(proc);
  }
  out = MakeLogic4VecVal(arena, 1, 0);
}

static void EvalProcessSuspend(Process* proc, SimContext& ctx, Arena& arena,
                               Logic4Vec& out) {
  if (IsRestrictedTarget(proc)) {
    ctx.GetDiag().Error(
        {},
        "suspend() shall only target a process created by an initial "
        "procedure, always procedure, or fork block");
    out = MakeLogic4VecVal(arena, 1, 0);
    return;
  }

  if (proc && proc == ctx.CurrentProcess() && ctx.InFunction()) {
    ctx.GetDiag().Error({}, "function cannot suspend its own execution");
    out = MakeLogic4VecVal(arena, 1, 0);
    return;
  }
  if (proc && proc->sv_state != ProcessState::kFinished &&
      proc->sv_state != ProcessState::kKilled) {
    proc->is_suspended = true;
    proc->sv_state = ProcessState::kSuspended;
  }
  out = MakeLogic4VecVal(arena, 1, 0);
}

// §9.7: drive a just-resumed process. Replay a delay wake that elapsed while it
// was suspended (its handle was stashed by the DelayAwaiter), resuming the
// exact parked continuation; if none is pending, the process was suspended
// while not waiting on an elapsed delay, so drive it through its own coro
// handle.
static void DriveResumedProcess(Process* target, SimContext& ctx) {
  if (!target->active) return;
  if (target->pending_wake) {
    auto h = target->pending_wake;
    target->pending_wake = {};
    if (!h.done()) {
      ctx.SetCurrentProcess(target);
      h.resume();
    }
    return;
  }
  if (!target->Done()) {
    ctx.SetCurrentProcess(target);
    target->Resume();
  }
}

static void EvalProcessResume(Process* proc, SimContext& ctx, Arena& arena,
                              Logic4Vec& out) {
  if (IsRestrictedTarget(proc)) {
    ctx.GetDiag().Error(
        {},
        "resume() shall only target a process created by an initial "
        "procedure, always procedure, or fork block");
    out = MakeLogic4VecVal(arena, 1, 0);
    return;
  }
  if (proc && proc->is_suspended) {
    proc->is_suspended = false;
    if (proc->sv_state == ProcessState::kSuspended) {
      proc->sv_state = ProcessState::kRunning;
    }

    auto* event = ctx.GetScheduler().GetEventPool().Acquire();
    Process* target = proc;
    event->callback = [target, &ctx]() { DriveResumedProcess(target, ctx); };
    ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), Region::kActive, event);
  }
  out = MakeLogic4VecVal(arena, 1, 0);
}

static void EvalProcessSrandom(Process* proc, const Expr* expr, SimContext& ctx,
                               Arena& arena, Logic4Vec& out) {
  if (proc && !expr->args.empty()) {
    auto seed_val = EvalExpr(expr->args[0], ctx, arena);
    auto seed = static_cast<uint32_t>(seed_val.ToUint64());
    proc->rng_seed = seed;
    // Reset the per-thread stream now so subsequent draws from this thread
    // replay the sequence keyed by the requested seed.
    proc->rng.seed(seed);
    proc->rng_initialized = true;
  }
  out = MakeLogic4VecVal(arena, 1, 0);
}

bool TryEvalProcessMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                              Logic4Vec& out) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts)) return false;
  if (ctx.GetVariableClassType(parts.var_name) != "process") return false;
  auto* var = ctx.FindVariable(parts.var_name);
  if (!var) return false;
  auto proc_handle = var->value.ToUint64();
  auto* proc = ctx.FindProcessByHandle(proc_handle);
  if (parts.method_name == "status") {
    uint64_t state_val = 0;
    if (proc) {
      ProcessState st = proc->sv_state;
      // §9.7: RUNNING means the process is executing right now (not inside a
      // blocking statement); WAITING means it is parked in one. Only the
      // process making this call is actually running -- any other process that
      // is still active and neither suspended nor terminated has yielded
      // control by blocking, so it is reported as WAITING rather than RUNNING.
      if (st == ProcessState::kRunning && proc->active &&
          proc != ctx.CurrentProcess()) {
        st = ProcessState::kWaiting;
      }
      state_val = static_cast<uint64_t>(st);
    }
    out = MakeLogic4VecVal(arena, 32, state_val);
    return true;
  }
  if (parts.method_name == "kill") {
    EvalProcessKill(proc, ctx, arena, out);
    return true;
  }
  if (parts.method_name == "suspend") {
    EvalProcessSuspend(proc, ctx, arena, out);
    return true;
  }
  if (parts.method_name == "srandom") {
    EvalProcessSrandom(proc, expr, ctx, arena, out);
    return true;
  }
  if (parts.method_name == "get_randstate") {
    // §18.13.4 via §9.7: retrieve the process RNG state as a string.
    out = StringToLogic4Vec(arena, proc ? ctx.GetRandState(proc) : "");
    return true;
  }
  if (parts.method_name == "set_randstate") {
    // §18.13.5 via §9.7: install a captured state string into the process RNG.
    // The argument is a string; read its raw bytes before deserializing.
    // Returns void.
    if (proc && !expr->args.empty()) {
      std::string state =
          Logic4VecToString(EvalExpr(expr->args[0], ctx, arena));
      ctx.SetRandState(proc, state);
    }
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  if (parts.method_name == "resume") {
    EvalProcessResume(proc, ctx, arena, out);
    return true;
  }
  return false;
}

}  // namespace delta
