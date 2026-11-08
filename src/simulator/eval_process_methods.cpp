#include <algorithm>
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
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/eval_callee_declaration.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_member_path.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer_register.h"
#include "simulator/process.h"
#include "simulator/process_termination.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

namespace delta {

static bool NamesProcessClass(const Expr* scope) {
  if (!scope) return false;
  if (scope->kind == ExprKind::kIdentifier) return scope->text == "process";
  return scope->kind == ExprKind::kMemberAccess && scope->is_scope_resolution &&
         scope->lhs && scope->lhs->kind == ExprKind::kIdentifier &&
         scope->lhs->text == "std" && scope->rhs &&
         scope->rhs->kind == ExprKind::kIdentifier &&
         scope->rhs->text == "process";
}

static bool NamesProcessSelf(const Expr* callee) {
  if (!callee || callee->kind != ExprKind::kMemberAccess) return false;
  if (!NamesProcessClass(callee->lhs)) return false;
  return callee->rhs && callee->rhs->kind == ExprKind::kIdentifier &&
         callee->rhs->text == "self";
}

bool TryEvalProcessStaticCall(const Expr* expr, SimContext& ctx, Arena& arena,
                              Logic4Vec& out) {
  if (!NamesProcessSelf(expr->lhs)) return false;
  auto* proc = ctx.CurrentProcess();
  if (!proc || proc->is_static_init) {
    out = MakeLogic4VecVal(arena, 64, 0);
    return true;
  }
  uint64_t handle = ctx.RegisterProcessHandle(proc);
  out = MakeLogic4VecVal(arena, 64, handle);
  return true;
}

static const Expr* SelectedName(const Expr* e) {
  while (e != nullptr && e->kind == ExprKind::kSelect) e = e->base;
  return e;
}

static const Variable* ProcessVariableOf(const Expr* access, SimContext& ctx,
                                         Arena& arena) {
  MethodCallParts parts;
  if (!ExtractHandleAccessParts(access, arena, parts)) return nullptr;
  if (ctx.GetVariableClassType(parts.var_name) != "process") return nullptr;
  return ctx.FindVariable(parts.var_name);
}

static bool ProcessTypedName(std::string_view name, SimContext& ctx) {
  if (ctx.GetVariableClassType(name) == "process") return true;
  const ClassObject* self = ctx.CurrentThis();
  if (self == nullptr || self->type == nullptr) return false;
  const auto* prop = self->type->FindProperty(name);
  return prop != nullptr && prop->type_name == "process";
}

static bool ProcessTypedField(const StructTypeInfo& layout,
                              std::string_view name) {
  return std::ranges::any_of(layout.fields, [name](const StructFieldInfo& f) {
    return f.name == name &&
           (f.type_name == "process" || f.type_name == "std::process");
  });
}

static bool ProcessTypedMember(const Expr* access, SimContext& ctx,
                               Arena& arena) {
  if (access->kind != ExprKind::kMemberAccess || access->is_scope_resolution ||
      access->lhs == nullptr || access->rhs == nullptr ||
      access->rhs->kind != ExprKind::kIdentifier) {
    return false;
  }
  if (const StructTypeInfo* layout = StructLayoutOfOperand(access->lhs, ctx))
    return ProcessTypedField(*layout, access->rhs->text);
  const ClassObject* obj =
      ctx.GetClassObject(EvalExpr(access->lhs, ctx, arena).ToUint64());
  if (obj == nullptr || obj->type == nullptr) return false;
  const auto* prop = obj->type->FindProperty(access->rhs->text);
  return prop != nullptr && prop->type_name == "process";
}

static bool CallAnswersProcess(const Expr* call, SimContext& ctx,
                               Arena& arena) {
  if (NamesProcessSelf(call->lhs)) return true;
  const DataType& result = *DeclarationOfCallee(call->lhs, ctx, arena).result;
  return UnitBuiltinClassKey(result) == "process";
}

bool NamesProcessHandle(const Expr* recv, SimContext& ctx, Arena& arena) {
  const Expr* name = SelectedName(recv);
  if (name == nullptr) return false;
  if (name->kind == ExprKind::kIdentifier)
    return ProcessTypedName(name->text, ctx);
  if (name->kind == ExprKind::kCall)
    return CallAnswersProcess(name, ctx, arena);
  return ProcessTypedMember(name, ctx, arena);
}

bool ResolveProcessMethodCall(const Expr* call, SimContext& ctx, Arena& arena,
                              ProcessMethodCall& out) {
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

static void KillProcessDescendants(Process* proc, SimContext& ctx) {
  std::vector<Process*> stack(proc->children.begin(), proc->children.end());
  while (!stack.empty()) {
    auto* child = stack.back();
    stack.pop_back();
    TerminateProcess(*child, ctx);
    for (auto* gc : child->children) stack.push_back(gc);
  }
}

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
  if (proc) {
    TerminateProcess(*proc, ctx);
    KillProcessDescendants(proc, ctx);
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
    const Region kRegion =
        target->is_reactive ? Region::kReactive : Region::kActive;
    ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), kRegion, event);
  }
  out = MakeLogic4VecVal(arena, 1, 0);
}

static void EvalProcessSrandom(Process* proc, const Expr* expr, SimContext& ctx,
                               Arena& arena, Logic4Vec& out) {
  if (proc && !expr->args.empty()) {
    auto seed_val = EvalExpr(expr->args[0], ctx, arena);
    auto seed = static_cast<uint32_t>(seed_val.ToUint64());
    proc->rng_seed = seed;
    proc->rng.seed(seed);
    proc->rng_initialized = true;
  }
  out = MakeLogic4VecVal(arena, 1, 0);
}

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

static void EvalProcessSetRandState(Process* proc, const Expr* expr,
                                    SimContext& ctx, Arena& arena,
                                    Logic4Vec& out) {
  if (proc && !expr->args.empty()) {
    std::string state = Logic4VecToString(EvalExpr(expr->args[0], ctx, arena));
    ctx.SetRandState(proc, state);
  }
  out = MakeLogic4VecVal(arena, 1, 0);
}

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
    out = StringToLogic4Vec(arena, proc ? ctx.GetRandState(proc) : "");
    out.is_string = true;
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
