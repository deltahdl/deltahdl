#include "simulator/stmt_exec.h"

#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "simulator/awaiters.h"
#include "simulator/awaiters_event_control.h"
#include "simulator/class_event_property.h"
#include "simulator/class_gc_roots.h"
#include "simulator/covergroup_instance.h"
#include "simulator/dpi_task_call.h"
#include "simulator/eval_call_result.h"
#include "simulator/eval_function_hier.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_instance_task.h"
#include "simulator/eval_mailbox.h"
#include "simulator/eval_semaphore.h"
#include "simulator/evaluation.h"
#include "simulator/exec_task.h"
#include "simulator/process.h"
#include "simulator/repeat_event_awaiter.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_coverage.h"
#include "simulator/static_aggregate.h"
#include "simulator/stmt_exec_internal.h"
#include "simulator/stmt_result.h"
#include "simulator/vcd_dump_state.h"
#include "simulator/vcd_writer.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_design_attach.h"
#include "simulator/vpi_globals.h"

namespace delta {

namespace {
struct ForkRendezvous {
  ForkJoinState* state;
  WaitForkState* parent_wfs;
  Process* parent_proc;
};
struct NbEventTrigger {
  Variable* var;
  std::string_view event_name;
  uint64_t count;
  bool reactive;
};

bool BuildEventTargetName(const Expr* expr, std::string& out) {
  if (!expr) return false;
  if (expr->kind == ExprKind::kIdentifier) {
    if (!expr->scope_prefix.empty()) {
      out += expr->scope_prefix;
      out += '.';
    }
    out += expr->text;
    return true;
  }
  if (expr->kind == ExprKind::kMemberAccess) {
    if (!BuildEventTargetName(expr->lhs, out)) return false;
    out += '.';
    return BuildEventTargetName(expr->rhs, out);
  }
  return false;
}

std::string_view ResolveEventTargetName(const Expr* expr, SimContext& ctx) {
  if (!expr) return {};
  if (expr->kind == ExprKind::kIdentifier) return expr->text;
  if (expr->kind != ExprKind::kMemberAccess) return {};
  std::string name;
  if (!BuildEventTargetName(expr, name)) name = HierarchicalReferenceName(expr);
  if (name.empty()) return {};
  auto* stored = ctx.GetArena().Create<std::string>(std::move(name));
  return *stored;
}
}  // namespace

static StmtResult ExecEventTriggerImpl(const Stmt* stmt, SimContext& ctx) {
  auto event_name = ResolveEventTargetName(stmt->expr, ctx);
  auto* var = TriggerTargetEvent(stmt->expr, event_name, ctx);
  if (!var || var->is_null_event) return StmtResult::kDone;
  if (!event_name.empty()) ctx.SetEventTriggered(event_name);
  TriggerEvent(var, ctx);
  return StmtResult::kDone;
}

static StmtResult ExecNbEventTriggerImpl(const Stmt* stmt, SimContext& ctx,
                                         Arena& arena);

void ExecEventTriggerInFunction(const Stmt* stmt, SimContext& ctx,
                                Arena& arena) {
  if (stmt->kind == StmtKind::kEventTrigger) {
    ExecEventTriggerImpl(stmt, ctx);
  } else if (stmt->kind == StmtKind::kNbEventTrigger) {
    ExecNbEventTriggerImpl(stmt, ctx, arena);
  }
}

static void ScheduleNbEventTrigger(Variable* var, std::string_view event_name,
                                   SimTime time, bool reactive,
                                   SimContext& ctx) {
  auto& sched = ctx.GetScheduler();
  auto* nba_event = sched.GetEventPool().Acquire();
  nba_event->callback = [var, event_name, reactive, &ctx]() {
    if (!event_name.empty()) ctx.SetEventTriggered(event_name);
    TriggerEventIn(var, ctx, reactive ? Region::kReactive : Region::kActive);
  };
  sched.ScheduleEvent(time, reactive ? Region::kReNBA : Region::kNBA,
                      nba_event);
}

static uint64_t EvalRepeatCount(const Expr* count_expr, SimContext& ctx,
                                Arena& arena);
static void SpawnNbaEventProcess(SimCoroutine coro, SimContext& ctx,
                                 Arena& arena);
static SimCoroutine NbEventTriggerEventCoroutine(const Stmt* stmt,
                                                 NbEventTrigger trigger,
                                                 SimContext& ctx, Arena& arena);

static StmtResult ExecNbEventTriggerImpl(const Stmt* stmt, SimContext& ctx,
                                         Arena& arena) {
  auto event_name = ResolveEventTargetName(stmt->expr, ctx);
  auto* var = TriggerTargetEvent(stmt->expr, event_name, ctx);
  if (!var || var->is_null_event) return StmtResult::kDone;

  bool reactive = ctx.IsReactiveContext();

  if (!stmt->events.empty()) {
    uint64_t count = 1;
    if (stmt->repeat_event_count) {
      count = EvalRepeatCount(stmt->repeat_event_count, ctx, arena);
      if (count == 0) {
        ScheduleNbEventTrigger(var, event_name, ctx.CurrentTime(), reactive,
                               ctx);
        return StmtResult::kDone;
      }
    }
    SpawnNbaEventProcess(
        NbEventTriggerEventCoroutine(stmt, {var, event_name, count, reactive},
                                     ctx, arena),
        ctx, arena);
    return StmtResult::kDone;
  }

  uint64_t delay = 0;
  if (stmt->delay) {
    delay = DelayExprToTicks(stmt->delay, ctx, arena);
  }
  auto time = ctx.CurrentTime();
  time.ticks += delay;
  ScheduleNbEventTrigger(var, event_name, time, reactive, ctx);
  return StmtResult::kDone;
}

static void FinalizeForkChildProcess(SimContext& ctx) {
  if (auto* child_proc = ctx.CurrentProcess()) child_proc->Finish();
  GetGlobalVpiContext().NoteThreadEnded(ctx.CurrentProcess());
}

static void DrainForkChild(SimContext& ctx, const ForkRendezvous& rdv) {
  auto* state = rdv.state;
  state->remaining--;
  bool should_resume =
      state->join_any ? !state->resumed : (state->remaining == 0);
  if (should_resume && state->parent) {
    state->resumed = true;
    if (state->parent_proc) ctx.SetCurrentProcess(state->parent_proc);
    state->parent.resume();
  }
  if (rdv.parent_wfs && --rdv.parent_wfs->remaining == 0 &&
      rdv.parent_wfs->waiter) {
    auto waiter = std::exchange(rdv.parent_wfs->waiter, {});
    ctx.SetCurrentProcess(rdv.parent_proc);
    waiter.resume();
  }
}

static SimCoroutine ForkChildCoroutine(const Stmt* body, SimContext& ctx,
                                       Arena& arena, Process* self) {
  co_await ExecStmt(body, ctx, arena);

  FinalizeForkChildProcess(ctx);
  self->ReleaseFromFork();
}

static bool IsForkBlockItemDecl(const Stmt* s) {
  return s->kind == StmtKind::kVarDecl || s->kind == StmtKind::kBlockItemDecl;
}

static void RegisterForkChildScopes(const Stmt* s, Process* p,
                                    SimContext& ctx) {
  if (s->kind == StmtKind::kExprStmt && s->expr) {
    std::string_view task_name;
    if (s->expr->kind == ExprKind::kCall)
      task_name = s->expr->callee;
    else if (s->expr->kind == ExprKind::kIdentifier)
      task_name = s->expr->text;
    if (!task_name.empty() && ctx.FindFunction(task_name))
      ctx.RegisterNamedScope(task_name, p);
  }
  if (s->kind == StmtKind::kBlock && !s->label.empty())
    ctx.RegisterNamedScope(s->label, p);
  for (auto scope : ctx.ActiveNamedScopes()) ctx.RegisterNamedScope(scope, p);
}

static Process* CreateForkChildProcess(SimContext& ctx, Arena& arena,
                                       Process* spawning_proc) {
  auto* p = arena.Create<Process>();
  if (spawning_proc) spawning_proc->children.push_back(p);
  p->kind = ProcessKind::kInitial;
  if (spawning_proc) {
    p->is_reactive = spawning_proc->is_reactive;
    p->home_region = spawning_proc->home_region;
    p->program_block_id = spawning_proc->program_block_id;
    p->inst_prefix = spawning_proc->inst_prefix;
    p->gen_prefixes = spawning_proc->gen_prefixes;
    p->gen_block_name = spawning_proc->gen_block_name;
    p->frame_owners = spawning_proc->frame_owners;
    p->spawned_in_named_scopes = spawning_proc->spawned_in_named_scopes;
    const std::vector<std::string_view>& spawner_in = ctx.ActiveNamedScopes();
    p->spawned_in_named_scopes.insert(p->spawned_in_named_scopes.end(),
                                      spawner_in.begin(), spawner_in.end());
  }
  ctx.CopyCarriedStacksTo(*p);
  p->rng_seed = ctx.DrawSeedForChild();
  GetGlobalVpiContext().NoteThreadCreated(p);
  return p;
}

static std::function<void()> MakeForkChildStartCallback(Process* p,
                                                        SimContext& ctx) {
  return [p, &ctx]() {
    if (!p->active) {
      p->ReleaseFromFork();
      return;
    }
    ctx.SetCurrentProcess(p);
    p->Resume();
  };
}

static void SpawnForkChild(const Stmt* s, SimContext& ctx, Arena& arena,
                           Process* spawning_proc, const ForkRendezvous& rdv) {
  if (rdv.parent_wfs) rdv.parent_wfs->remaining++;
  auto* p = CreateForkChildProcess(ctx, arena, spawning_proc);
  p->origin = s;
  p->fork_release = [&ctx, rdv]() { DrainForkChild(ctx, rdv); };
  p->coro = ForkChildCoroutine(s, ctx, arena, p).Release();

  RegisterForkChildScopes(s, p, ctx);
  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  event->callback = MakeForkChildStartCallback(p, ctx);
  auto fork_region = (spawning_proc && spawning_proc->is_reactive)
                         ? Region::kReactive
                         : Region::kActive;
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), fork_region, event);
}

static void SpawnForkChildren(const Stmt* stmt, SimContext& ctx, Arena& arena,
                              Process* spawning_proc,
                              const ForkRendezvous& rdv) {
  for (auto* s : stmt->fork_stmts) {
    if (IsForkBlockItemDecl(s)) continue;
    SpawnForkChild(s, ctx, arena, spawning_proc, rdv);
  }
}

static ExecTask AwaitForkJoin(ForkJoinState* state) {
  co_await ForkJoinAwaiter{state};
  co_return StmtResult::kDone;
}

static void EnterForkLabelScope(const Stmt* stmt, SimContext& ctx,
                                Arena& arena) {
  ctx.PushStaticScope(ctx.StmtFrameName(stmt));
  RestoreBlockAggregates(*stmt, ctx.StmtFrameName(stmt), ctx);
  ctx.PushActiveNamedScope(stmt->label);
  ctx.Vcd().SetVcdScopeKind(ActiveNamedScopePath(ctx), VcdScopeKind::kFork);
  ctx.RegisterNamedScope(stmt->label, ctx.CurrentProcess());
  SampleAtBlockEvent(stmt->label, true, ctx, arena);
}

static void ExitForkLabelScope(const Stmt* stmt, SimContext& ctx, Arena& arena,
                               bool ended) {
  if (ended) SampleAtBlockEvent(stmt->label, false, ctx, arena);
  ctx.UnregisterNamedScope(stmt->label, ctx.CurrentProcess());
  ctx.PopActiveNamedScope();
  RetainBlockAggregates(*stmt, ctx.StmtFrameName(stmt), ctx, arena);
  ctx.PopStaticScope(ctx.StmtFrameName(stmt));
}

static ExecTask ExecFork(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) EnterForkLabelScope(stmt, ctx, arena);

  uint32_t process_count = 0;
  for (auto* s : stmt->fork_stmts) {
    if (IsForkBlockItemDecl(s)) {
      co_await ExecStmt(s, ctx, arena);
    } else {
      process_count++;
    }
  }

  StmtResult result = StmtResult::kDone;
  if (process_count != 0) {
    auto* state = arena.Create<ForkJoinState>();
    state->remaining = process_count;
    state->join_any = (stmt->join_kind == TokenKind::kKwJoinAny);

    auto* spawning_proc = ctx.CurrentProcess();
    state->parent_proc = spawning_proc;

    Process* parent_proc = spawning_proc;
    WaitForkState* parent_wfs =
        parent_proc ? &parent_proc->wait_fork_state : nullptr;

    SpawnForkChildren(stmt, ctx, arena, spawning_proc,
                      {state, parent_wfs, parent_proc});

    if (stmt->join_kind != TokenKind::kKwJoinNone) {
      result = co_await AwaitForkJoin(state);
    }
  }
  if (labeled) {
    ExitForkLabelScope(stmt, ctx, arena, result != StmtResult::kDisable);
    if (result == StmtResult::kDisable &&
        ctx.GetDisableTarget() == stmt->label) {
      ctx.ClearDisableTarget();
      result = StmtResult::kDone;
    }
  }
  co_return result;
}

void SpawnForkJoinNone(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt || stmt->join_kind != TokenKind::kKwJoinNone) return;
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(ctx.StmtFrameName(stmt));

  uint32_t process_count = 0;
  for (auto* s : stmt->fork_stmts) {
    if (!IsForkBlockItemDecl(s)) process_count++;
  }
  if (process_count == 0) {
    if (labeled) ctx.PopStaticScope(ctx.StmtFrameName(stmt));
    return;
  }

  auto* state = arena.Create<ForkJoinState>();
  state->remaining = process_count;
  state->join_any = false;
  auto* spawning_proc = ctx.CurrentProcess();
  state->parent_proc = spawning_proc;
  WaitForkState* parent_wfs =
      spawning_proc ? &spawning_proc->wait_fork_state : nullptr;
  SpawnForkChildren(stmt, ctx, arena, spawning_proc,
                    {state, parent_wfs, spawning_proc});
  if (labeled) ctx.PopStaticScope(ctx.StmtFrameName(stmt));
}

static ExecTask ExecWaitFork(SimContext& ctx) {
  auto* proc = ctx.CurrentProcess();
  if (!proc) co_return StmtResult::kDone;
  bool suspends = proc->wait_fork_state.remaining != 0;
  co_await WaitForkAwaiter{&proc->wait_fork_state};
  if (suspends) ctx.FlushPendingViolations();
  co_return StmtResult::kDone;
}

static void UnregisterTaskNamedScope(const ModuleItem* func, SimContext& ctx) {
  ctx.PopActiveNamedScope();
  ctx.UnregisterNamedScope(func->name, ctx.CurrentProcess());
}

enum class InlineTaskDisable : std::uint8_t {
  kStopHere,
  kPropagate,
};

static InlineTaskDisable HandleInlineTaskDisable(const ModuleItem* func,
                                                 const Expr* expr,
                                                 bool has_name, SimContext& ctx,
                                                 Arena& arena) {
  if (has_name && ctx.GetDisableTarget() == func->name) {
    ctx.ClearDisableTarget();
    return InlineTaskDisable::kStopHere;
  }
  if (has_name) UnregisterTaskNamedScope(func, ctx);
  TeardownTaskCall(func, expr, ctx, arena);
  return InlineTaskDisable::kPropagate;
}

static ExecTask ExecInlineTaskBody(const ModuleItem* func, const Expr* expr,
                                   SimContext& ctx, Arena& arena) {
  VpiActiveFrameScope frame(expr);
  bool has_name = !func->name.empty();
  for (auto* s : func->func_body_stmts) {
    auto result = co_await ExecStmt(s, ctx, arena);
    if (result == StmtResult::kReturn) break;
    if (result == StmtResult::kDisable) {
      if (HandleInlineTaskDisable(func, expr, has_name, ctx, arena) ==
          InlineTaskDisable::kStopHere) {
        co_return StmtResult::kDone;
      }
      co_return StmtResult::kDisable;
    }
    if (ctx.StopRequested()) co_return StmtResult::kDone;
  }
  if (has_name) SampleAtBlockEvent(func->name, false, ctx, arena);
  co_return StmtResult::kDone;
}

static bool ExecNonSuspendingCall(const Expr* expr, SimContext& ctx,
                                  Arena& arena) {
  if (TryExecSystemCallTask(expr, ctx, arena)) return true;
  if (!IsModeMethodCall(expr)) return false;
  ExecCallStmtExpr(expr, ctx, arena);
  return true;
}

enum class WaitingCall : std::uint8_t { kNone, kProcess, kSemaphore, kMailbox };

static WaitingCall ClassifyWaitingCall(const Expr* expr, SimContext& ctx,
                                       Arena& arena) {
  if (IsSuspendingProcessCall(expr, ctx, arena)) return WaitingCall::kProcess;
  if (SemaphoreCallTarget(expr, ctx, "get") != nullptr)
    return WaitingCall::kSemaphore;
  if (IsMailboxBlockingCall(expr, ctx, arena)) return WaitingCall::kMailbox;
  return WaitingCall::kNone;
}

static ExecTask ExecWaitingCall(WaitingCall kind, const Expr* expr,
                                CallResultReceiverScope& held, SimContext& ctx,
                                Arena& arena) {
  if (kind == WaitingCall::kProcess) {
    co_return co_await ExecSuspendingProcessCall(expr, ctx, arena, held);
  }
  if (kind == WaitingCall::kMailbox) {
    co_return co_await ExecMailboxCall(expr, ctx, arena, held);
  }
  auto* sem = SemaphoreCallTarget(expr, ctx, "get");
  int32_t count = SemaphoreKeyArg(expr, ctx, arena, 1);
  held.Release();
  if (ReportNegativeKeyCount(expr, count, "15.3.3", ctx)) {
    co_return StmtResult::kDone;
  }
  co_await SemaphoreGetAwaiter{.sem = *sem, .count = count, .ctx = &ctx};
  co_return StmtResult::kDone;
}

static ExecTask ExecInlineTaskCall(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  auto* expr = stmt->expr;

  if (ExecNonSuspendingCall(expr, ctx, arena)) co_return StmtResult::kDone;

  CallResultReceiverScope receiver(expr, ctx, arena);
  WaitingCall waiting = ClassifyWaitingCall(expr, ctx, arena);
  if (waiting != WaitingCall::kNone) {
    co_return co_await ExecWaitingCall(waiting, expr, receiver, ctx, arena);
  }
  InstanceMethodInfo instance_call;
  bool enables_task = SetupInstanceTaskCall(expr, ctx, arena, instance_call);
  if (!enables_task && receiver.Holds()) {
    ExecCallStmtExpr(expr, ctx, arena);
    co_return StmtResult::kDone;
  }
  receiver.Release();
  if (enables_task) {
    co_return co_await ExecInstanceTaskCall(instance_call, expr, ctx, arena);
  }
  if (const Stmt* fork = ExternForkjoinCall(expr, ctx, arena)) {
    co_return co_await ExecStmt(fork, ctx, arena);
  }
  auto* func = ctx.EnterSubroutinePackage(SetupTaskCall(expr, ctx, arena));
  if (!func) {
    if (EnablesDpiImportTask(expr, ctx)) {
      co_return co_await ExecDpiImportTask(expr, ctx, arena);
    }
    ExecCallStmtExpr(expr, ctx, arena);
    co_return StmtResult::kDone;
  }
  bool has_name = !func->name.empty();
  if (has_name) {
    ctx.RegisterNamedScope(func->name, ctx.CurrentProcess());
    ctx.PushActiveNamedScope(func->name);
    SampleAtBlockEvent(func->name, true, ctx, arena);
  }
  StmtResult outcome = co_await ExecInlineTaskBody(func, expr, ctx, arena);
  if (outcome == StmtResult::kDisable) co_return StmtResult::kDisable;
  if (has_name) UnregisterTaskNamedScope(func, ctx);
  TeardownTaskCall(func, expr, ctx, arena);
  co_return StmtResult::kDone;
}

static ExecTask ExecBlockingAssignTimed(const Stmt* stmt, SimContext& ctx,
                                        Arena& arena) {
  auto [rhs_val, pin] = PinValue(ctx, EvalExpr(stmt->rhs, ctx, arena));
  co_await DelayAwaiter{ctx, DelayExprToTicks(stmt->delay, ctx, arena)};
  PerformBlockingAssign(stmt->lhs, rhs_val, ctx, arena);
  co_return StmtResult::kDone;
}

static ExecTask ExecBlockingAssignEvent(const Stmt* stmt, SimContext& ctx,
                                        Arena& arena) {
  auto [rhs_val, pin] = PinValue(ctx, EvalExpr(stmt->rhs, ctx, arena));
  co_await EventAwaiter{ctx, stmt->events, arena};
  ctx.FlushPendingViolations();
  PerformBlockingAssign(stmt->lhs, rhs_val, ctx, arena);
  co_return StmtResult::kDone;
}

static uint64_t EvalRepeatCount(const Expr* count_expr, SimContext& ctx,
                                Arena& arena) {
  return RepeatIterationCount(EvalExpr(count_expr, ctx, arena));
}

static ExecTask ExecBlockingAssignRepeatEvent(const Stmt* stmt, SimContext& ctx,
                                              Arena& arena) {
  auto [rhs_val, pin] = PinValue(ctx, EvalExpr(stmt->rhs, ctx, arena));
  uint64_t count = EvalRepeatCount(stmt->repeat_event_count, ctx, arena);
  if (count > 0) {
    co_await RepeatEventAwaiter{ctx, stmt->events, arena, count};
    ctx.FlushPendingViolations();
  }
  PerformBlockingAssign(stmt->lhs, rhs_val, ctx, arena);
  co_return StmtResult::kDone;
}

static SimCoroutine NbaEventCoroutine(const Stmt* stmt,
                                      const Scheduler::NbaCapture* updates,
                                      SimContext& ctx, Arena& arena) {
  co_await EventAwaiter{ctx, stmt->events, arena};
  ReleaseNbaUpdates(*updates, ctx);
}

static SimCoroutine NbaRepeatEventCoroutine(
    const Stmt* stmt, const Scheduler::NbaCapture* updates, uint64_t count,
    SimContext& ctx, Arena& arena) {
  co_await RepeatEventAwaiter{ctx, stmt->events, arena, count};
  ReleaseNbaUpdates(*updates, ctx);
}

static void SpawnNbaEventProcess(SimCoroutine coro, SimContext& ctx,
                                 Arena& arena) {
  auto* p = arena.Create<Process>();
  p->kind = ProcessKind::kInitial;
  p->coro = coro.Release();
  auto* parent = ctx.CurrentProcess();
  if (parent && parent->is_reactive) {
    p->is_reactive = true;
    p->home_region = Region::kReactive;
  }
  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  event->callback = [p, &ctx]() {
    ctx.SetCurrentProcess(p);
    p->Resume();
  };
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), p->home_region, event);
}

static StmtResult ExecNbaWithEvent(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  const Scheduler::NbaCapture* updates = CaptureNonblockingAssign(
      stmt, SampleNonblockingRhs(stmt, ctx, arena), ctx, arena);
  if (stmt->repeat_event_count) {
    uint64_t count = EvalRepeatCount(stmt->repeat_event_count, ctx, arena);
    if (count == 0) {
      ReleaseNbaUpdates(*updates, ctx);
      return StmtResult::kDone;
    }
    SpawnNbaEventProcess(
        NbaRepeatEventCoroutine(stmt, updates, count, ctx, arena), ctx, arena);
  } else {
    SpawnNbaEventProcess(NbaEventCoroutine(stmt, updates, ctx, arena), ctx,
                         arena);
  }
  return StmtResult::kDone;
}

static SimCoroutine NbEventTriggerEventCoroutine(const Stmt* stmt,
                                                 NbEventTrigger trigger,
                                                 SimContext& ctx,
                                                 Arena& arena) {
  for (uint64_t i = 0; i < trigger.count; ++i) {
    co_await EventAwaiter{ctx, stmt->events, arena};
  }
  ScheduleNbEventTrigger(trigger.var, trigger.event_name, ctx.CurrentTime(),
                         trigger.reactive, ctx);
}

static ExecTask DispatchBlockingAssign(const Stmt* stmt, SimContext& ctx,
                                       Arena& arena) {
  if (stmt->delay) return ExecBlockingAssignTimed(stmt, ctx, arena);
  if (!stmt->events.empty()) {
    if (stmt->repeat_event_count)
      return ExecBlockingAssignRepeatEvent(stmt, ctx, arena);
    return ExecBlockingAssignEvent(stmt, ctx, arena);
  }
  return ExecTask::Immediate(ExecImmediateBlockingAssign(stmt, ctx, arena));
}

static StmtResult DispatchReturn(const Stmt* stmt, SimContext& ctx,
                                 Arena& arena) {
  if (stmt->expr && ctx.RsReturnSlot() != nullptr) {
    Logic4Vec* slot = ctx.RsReturnSlot();
    uint32_t width = slot->width;
    *slot =
        ResizeToWidth(EvalExpr(stmt->expr, ctx, arena, width), width, arena);
  }
  return StmtResult::kReturn;
}

static ExecTask ExecStmtDispatch(const Stmt* stmt, SimContext& ctx,
                                 Arena& arena) {
  switch (stmt->kind) {
    case StmtKind::kNull:
      return ExecTask::Immediate(StmtResult::kDone);
    case StmtKind::kBlock:
      return ExecBlock(stmt, ctx, arena);
    case StmtKind::kIf:
      return ExecIf(stmt, ctx, arena);
    case StmtKind::kCase:
      return ExecCase(stmt, ctx, arena);
    case StmtKind::kFor:
      return ExecFor(stmt, ctx, arena);
    case StmtKind::kForeach:
      return ExecForeach(stmt, ctx, arena);
    case StmtKind::kWhile:
      return ExecWhile(stmt, ctx, arena);
    case StmtKind::kForever:
      return ExecForever(stmt, ctx, arena);
    case StmtKind::kRepeat:
      return ExecRepeat(stmt, ctx, arena);
    case StmtKind::kDoWhile:
      return ExecDoWhile(stmt, ctx, arena);
    case StmtKind::kBlockingAssign:
      return DispatchBlockingAssign(stmt, ctx, arena);
    case StmtKind::kNonblockingAssign:
      if (!stmt->events.empty())
        return ExecTask::Immediate(ExecNbaWithEvent(stmt, ctx, arena));
      return ExecTask::Immediate(ExecNonblockingAssignImpl(stmt, ctx, arena));
    case StmtKind::kExprStmt:
      return ExecInlineTaskCall(stmt, ctx, arena);
    case StmtKind::kDelay:
      return ExecDelay(stmt, ctx, arena);
    case StmtKind::kCycleDelay:
      return ExecCycleDelay(stmt, ctx, arena);
    case StmtKind::kEventControl:
      return ExecEventControl(stmt, ctx, arena);
    case StmtKind::kFork:
      return ExecFork(stmt, ctx, arena);
    case StmtKind::kWait:
      return ExecWait(stmt, ctx, arena);
    case StmtKind::kEventTrigger:
      return ExecTask::Immediate(ExecEventTriggerImpl(stmt, ctx));
    case StmtKind::kNbEventTrigger:
      return ExecTask::Immediate(ExecNbEventTriggerImpl(stmt, ctx, arena));
    case StmtKind::kWaitOrder:
      return ExecWaitOrder(stmt, ctx, arena);
    case StmtKind::kTimingControl:
      return ExecTask::Immediate(StmtResult::kDone);
    case StmtKind::kDisable:
      return ExecTask::Immediate(ExecDisableImpl(stmt, ctx));
    case StmtKind::kDisableFork:
      return ExecTask::Immediate(ExecDisableForkImpl(ctx));
    case StmtKind::kWaitFork:
      return ExecWaitFork(ctx);
    case StmtKind::kBreak:
      return ExecTask::Immediate(StmtResult::kBreak);
    case StmtKind::kContinue:
      return ExecTask::Immediate(StmtResult::kContinue);
    case StmtKind::kReturn:
      return ExecTask::Immediate(DispatchReturn(stmt, ctx, arena));
    case StmtKind::kAssertImmediate:
    case StmtKind::kAssumeImmediate:
    case StmtKind::kCoverImmediate:
      return ExecImmediateAssert(stmt, ctx, arena);
    case StmtKind::kExpect:
      return ExecExpect(stmt, ctx, arena);
    case StmtKind::kCheckerInstantiation:
      return ExecCheckerInstantiation(stmt, ctx, arena);
    case StmtKind::kForce:
    case StmtKind::kAssign:
      return ExecTask::Immediate(ExecForceOrAssignImpl(stmt, ctx, arena));
    case StmtKind::kRelease:
    case StmtKind::kDeassign:
      return ExecTask::Immediate(ExecReleaseOrDeassignImpl(stmt, ctx, arena));
    case StmtKind::kRandcase:
      return ExecRandcase(stmt, ctx, arena);
    case StmtKind::kRandsequence:
      return ExecRandsequence(stmt, ctx, arena);
    case StmtKind::kVarDecl:
    case StmtKind::kBlockItemDecl:
      return ExecTask::Immediate(ExecVarDeclImpl(stmt, ctx, arena));
    default:
      return ExecTask::Immediate(StmtResult::kDone);
  }
}

static ExecTask ExecLabeledStmt(const Stmt* stmt, SimContext& ctx,
                                Arena& arena) {
  ctx.PushActiveNamedScope(stmt->label);
  ctx.RegisterNamedScope(stmt->label, ctx.CurrentProcess());
  auto result = co_await ExecStmtDispatch(stmt, ctx, arena);
  ctx.UnregisterNamedScope(stmt->label, ctx.CurrentProcess());
  ctx.PopActiveNamedScope();
  if (result == StmtResult::kDisable && ctx.GetDisableTarget() == stmt->label) {
    ctx.ClearDisableTarget();
    result = StmtResult::kDone;
  }
  co_return result;
}

ExecTask ExecStmt(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt || CurrentProcessEnded(ctx)) {
    return ExecTask::Immediate(StmtResult::kDone);
  }
  GetGlobalVpiContext().NoteStmtExecuting(stmt, ctx.ActiveInstancePrefix());
  NoteStatementExecuted(stmt, ctx);
  if (!stmt->label.empty() && stmt->kind != StmtKind::kBlock &&
      stmt->kind != StmtKind::kFork) {
    return ExecLabeledStmt(stmt, ctx, arena);
  }
  return ExecStmtDispatch(stmt, ctx, arena);
}

}  // namespace delta
