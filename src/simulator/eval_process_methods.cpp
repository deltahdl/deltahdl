#include <coroutine>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/class_object.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer_register.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

namespace delta {

// §26.7 with Syntax 26-5: a built-in class may be named bare, `process`, or
// explicitly through the built-in package, `std::process`, the second parsing
// as a scope resolution of the two identifiers; both name the one class of
// §9.7.
static bool NamesProcessClass(const Expr* scope) {
  if (!scope) return false;
  if (scope->kind == ExprKind::kIdentifier) return scope->text == "process";
  return scope->kind == ExprKind::kMemberAccess && scope->is_scope_resolution &&
         scope->lhs && scope->lhs->kind == ExprKind::kIdentifier &&
         scope->lhs->text == "std" && scope->rhs &&
         scope->rhs->kind == ExprKind::kIdentifier &&
         scope->rhs->text == "process";
}

bool TryEvalProcessStaticCall(const Expr* expr, SimContext& ctx, Arena& arena,
                              Logic4Vec& out) {
  if (!expr->lhs || expr->lhs->kind != ExprKind::kMemberAccess) return false;
  auto* access = expr->lhs;
  if (!NamesProcessClass(access->lhs)) return false;
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

// The name an element select reads from: `arr` for `arr[i]` and `m[i][j]`.
static const Expr* SelectedName(const Expr* e) {
  while (e != nullptr && e->kind == ExprKind::kSelect) e = e->base;
  return e;
}

// A process handle a method select names by a variable's key: `p`, or
// `p::proc` under the key ExtractHandleAccessParts answers (§26.3).
static const Variable* ProcessVariableOf(const Expr* access, SimContext& ctx,
                                         Arena& arena) {
  MethodCallParts parts;
  if (!ExtractHandleAccessParts(access, arena, parts)) return nullptr;
  if (ctx.GetVariableClassType(parts.var_name) != "process") return nullptr;
  return ctx.FindVariable(parts.var_name);
}

// Whether the bare name `name` is declared with the process class: a variable,
// or a property of the running object (§8.6).
static bool ProcessTypedName(std::string_view name, SimContext& ctx) {
  if (ctx.GetVariableClassType(name) == "process") return true;
  const ClassObject* self = ctx.CurrentThis();
  if (self == nullptr || self->type == nullptr) return false;
  const auto* prop = self->type->FindProperty(name);
  return prop != nullptr && prop->type_name == "process";
}

// Whether `access`, a property selected through a handle, `w.q`, is declared
// with the process class by the class of the object the handle holds.
static bool ProcessTypedMember(const Expr* access, SimContext& ctx,
                               Arena& arena) {
  if (access->kind != ExprKind::kMemberAccess || access->is_scope_resolution ||
      access->lhs == nullptr || access->rhs == nullptr ||
      access->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  const ClassObject* obj =
      ctx.GetClassObject(EvalExpr(access->lhs, ctx, arena).ToUint64());
  if (obj == nullptr || obj->type == nullptr) return false;
  const auto* prop = obj->type->FindProperty(access->rhs->text);
  return prop != nullptr && prop->type_name == "process";
}

bool NamesProcessHandle(const Expr* recv, SimContext& ctx, Arena& arena) {
  const Expr* name = SelectedName(recv);
  if (name == nullptr) return false;
  if (name->kind == ExprKind::kIdentifier)
    return ProcessTypedName(name->text, ctx);
  return ProcessTypedMember(name, ctx, arena);
}

bool ResolveProcessMethodCall(const Expr* call, SimContext& ctx, Arena& arena,
                              ProcessMethodCall& out) {
  // A.8.2 makes the argument list of a method call optional, so `p.kill` is
  // the call as `p.kill()` is; the select is the call's callee or the call.
  const Expr* access = call;
  if (call != nullptr && call->kind == ExprKind::kCall) access = call->lhs;
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      access->is_scope_resolution || access->lhs == nullptr ||
      access->rhs == nullptr || access->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  uint64_t handle = 0;
  if (const Variable* var = ProcessVariableOf(access, ctx, arena)) {
    handle = var->value.ToUint64();
  } else if (NamesProcessHandle(access->lhs, ctx, arena)) {
    handle = EvalExpr(access->lhs, ctx, arena).ToUint64();
  } else {
    return false;
  }
  out.proc = ctx.FindProcessByHandle(handle);
  out.method = access->rhs->text;
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

// `loc` is where the call was written. A Process carries no position -- it is
// a running thread rather than a piece of source -- so a report about the
// process this call names has to be given the call's own position.
static void EvalProcessKill(Process* proc, SimContext& ctx, Arena& arena,
                            Logic4Vec& out, SourceLoc loc) {
  if (IsRestrictedTarget(proc)) {
    ctx.GetDiag().Error(
        loc,
        "kill() acts only on a process begun by an initial or always "
        "procedure or by a fork block within one",
        Subclause("9.7"));
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
                               Logic4Vec& out, SourceLoc loc) {
  if (IsRestrictedTarget(proc)) {
    ctx.GetDiag().Error(
        loc,
        "suspend() acts only on a process begun by an initial or always "
        "procedure or by a fork block within one",
        Subclause("9.7"));
    out = MakeLogic4VecVal(arena, 1, 0);
    return;
  }

  if (proc && proc == ctx.CurrentProcess() && ctx.InFunction()) {
    ctx.GetDiag().Error(loc, "function cannot suspend its own execution",
                        Subclause("9.7"));
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

// §9.7: drive a just-resumed process. A wake that came while it was suspended
// -- a delay that elapsed, or the process's own suspend() -- was stashed as the
// parked continuation, and is replayed; a start that found it suspended is
// run. Otherwise the process is still blocked where it was, resensitized, and
// the wait it is parked in wakes it: resuming Process::coro there would resume
// the outer frame beneath the one that is parked.
static void DriveResumedProcess(Process* target, SimContext& ctx) {
  if (!target->active) return;
  std::coroutine_handle<> h = target->pending_wake;
  target->pending_wake = {};
  if (h && !h.done()) {
    ctx.SetCurrentProcess(target);
    h.resume();
    return;
  }
  if (target->start_deferred) {
    target->start_deferred = false;
    ctx.SetCurrentProcess(target);
    target->Resume();
  }
}

static void EvalProcessResume(Process* proc, SimContext& ctx, Arena& arena,
                              Logic4Vec& out, SourceLoc loc) {
  if (IsRestrictedTarget(proc)) {
    ctx.GetDiag().Error(
        loc,
        "resume() acts only on a process begun by an initial or always "
        "procedure or by a fork block within one",
        Subclause("9.7"));
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

// §9.7: RUNNING means the process is executing right now (not inside a blocking
// statement); WAITING means it is parked in one. Only the process making the
// call is actually running -- any other process that is still active and
// neither suspended nor terminated has yielded control by blocking, so it is
// reported as WAITING rather than RUNNING. A handle naming no live process
// reports the zero state.
static uint64_t ObservedProcessState(const Process* proc,
                                     const SimContext& ctx) {
  if (!proc) return 0;
  ProcessState st = proc->sv_state;
  if (st == ProcessState::kRunning && proc->active &&
      proc != ctx.CurrentProcess()) {
    st = ProcessState::kWaiting;
  }
  return static_cast<uint64_t>(st);
}

// §18.13.5 via §9.7: install a captured state string into the process RNG. The
// argument is a string; its raw bytes are read before deserializing. Void.
static void EvalProcessSetRandState(Process* proc, const Expr* expr,
                                    SimContext& ctx, Arena& arena,
                                    Logic4Vec& out) {
  if (proc && !expr->args.empty()) {
    std::string state = Logic4VecToString(EvalExpr(expr->args[0], ctx, arena));
    ctx.SetRandState(proc, state);
  }
  out = MakeLogic4VecVal(arena, 1, 0);
}

// §26.3 admits a package-qualified handle as the receiver, `p::proc.kill()`,
// resolved by the key ExtractHandleMethodCallParts answers.
bool TryEvalProcessMethodWithoutArgs(const Expr* expr, SimContext& ctx,
                                     Arena& arena, Logic4Vec& out) {
  return TryEvalProcessMethodCall(expr, ctx, arena, out);
}

bool TryEvalProcessMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                              Logic4Vec& out) {
  ProcessMethodCall call;
  if (!ResolveProcessMethodCall(expr, ctx, arena, call)) return false;
  Process* proc = call.proc;
  std::string_view method = call.method;
  if (method == "status") {
    out = MakeLogic4VecVal(arena, 32, ObservedProcessState(proc, ctx));
    return true;
  }
  if (method == "kill") {
    EvalProcessKill(proc, ctx, arena, out, expr->range.start);
    return true;
  }
  if (method == "suspend") {
    EvalProcessSuspend(proc, ctx, arena, out, expr->range.start);
    return true;
  }
  if (method == "srandom") {
    EvalProcessSrandom(proc, expr, ctx, arena, out);
    return true;
  }
  if (method == "get_randstate") {
    // §18.13.4 via §9.7: retrieve the process RNG state as a string.
    out = StringToLogic4Vec(arena, proc ? ctx.GetRandState(proc) : "");
    return true;
  }
  if (method == "set_randstate") {
    EvalProcessSetRandState(proc, expr, ctx, arena, out);
    return true;
  }
  if (method == "resume") {
    EvalProcessResume(proc, ctx, arena, out, expr->range.start);
    return true;
  }
  return false;
}

void RegisterProcessClassType(SimContext& ctx, Arena& arena) {
  auto* proc_type = arena.Create<ClassTypeInfo>();
  proc_type->name = "process";
  proc_type->enum_members["FINISHED"] = 0;
  proc_type->enum_members["RUNNING"] = 1;
  proc_type->enum_members["WAITING"] = 2;
  proc_type->enum_members["SUSPENDED"] = 3;
  proc_type->enum_members["KILLED"] = 4;
  ctx.RegisterClassType("process", proc_type);
  // §9.7 with §6.19.5.6: the enumeration `process::state` that status()
  // answers, so name() on a status value, chained or held in a variable
  // declared with the type, yields the member's name.
  EnumTypeInfo state;
  state.type_name = "process::state";
  for (const char* name :
       {"FINISHED", "RUNNING", "WAITING", "SUSPENDED", "KILLED"}) {
    state.members.push_back(
        {name, static_cast<uint64_t>(state.members.size()), 0});
  }
  ctx.RegisterEnumType(state.type_name, state);
}

}  // namespace delta
