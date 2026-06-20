#include "simulator/stmt_exec.h"

#include <cmath>
#include <cstdint>
#include <cstring>
#include <iostream>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/awaiters.h"
#include "simulator/evaluation.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/stmt_exec_internal.h"

namespace delta {

static StmtResult ExecEventTriggerImpl(const Stmt* stmt, SimContext& ctx) {
  if (!stmt->expr || stmt->expr->kind != ExprKind::kIdentifier) {
    return StmtResult::kDone;
  }
  auto* var = ctx.FindVariable(stmt->expr->text);
  if (!var) return StmtResult::kDone;

  if (var->is_null_event) return StmtResult::kDone;

  ctx.SetEventTriggered(stmt->expr->text);

  auto pending = std::move(var->watchers);
  var->watchers.clear();
  auto& sched = ctx.GetScheduler();
  auto region = ctx.IsReactiveContext() ? Region::kReactive : Region::kActive;
  for (auto& cb : pending) {
    auto* event = sched.GetEventPool().Acquire();
    event->callback = std::move(cb);
    sched.ScheduleEvent(ctx.CurrentTime(), region, event);
  }
  return StmtResult::kDone;
}

// Schedules the nonblocking-assignment-region update event that fires a named
// event: it marks the event triggered and wakes every process waiting on it.
// Shared by both the delay/immediate and the event-control forms of ->>.
static void ScheduleNbEventTrigger(Variable* var, std::string_view event_name,
                                   SimTime time, bool reactive,
                                   SimContext& ctx) {
  auto& sched = ctx.GetScheduler();
  auto* nba_event = sched.GetEventPool().Acquire();
  nba_event->callback = [var, event_name, reactive, &ctx]() {
    ctx.SetEventTriggered(event_name);
    auto pending = std::move(var->watchers);
    var->watchers.clear();
    auto& s = ctx.GetScheduler();
    auto wake_region = reactive ? Region::kReactive : Region::kActive;
    for (auto& cb : pending) {
      auto* ev = s.GetEventPool().Acquire();
      ev->callback = std::move(cb);
      s.ScheduleEvent(ctx.CurrentTime(), wake_region, ev);
    }
  };
  sched.ScheduleEvent(time, reactive ? Region::kReNBA : Region::kNBA,
                      nba_event);
}

// The event-control form of ->> reuses the same detached-process machinery that
// an intra-assignment event on a nonblocking assignment uses; declared here,
// defined alongside that machinery below.
static uint64_t EvalRepeatCount(const Expr* count_expr, SimContext& ctx,
                                Arena& arena);
static void SpawnNbaEventProcess(SimCoroutine coro, SimContext& ctx,
                                 Arena& arena);
static SimCoroutine NbEventTriggerEventCoroutine(const Stmt* stmt,
                                                 Variable* var,
                                                 std::string_view event_name,
                                                 uint64_t count, bool reactive,
                                                 SimContext& ctx, Arena& arena);

static StmtResult ExecNbEventTriggerImpl(const Stmt* stmt, SimContext& ctx,
                                         Arena& arena) {
  if (!stmt->expr || stmt->expr->kind != ExprKind::kIdentifier) {
    return StmtResult::kDone;
  }
  auto* var = ctx.FindVariable(stmt->expr->text);
  if (!var) return StmtResult::kDone;

  if (var->is_null_event) return StmtResult::kDone;

  auto event_name = stmt->expr->text;
  bool reactive = ctx.IsReactiveContext();

  // Event-control form: ->> @(...) ev  or  ->> repeat(n) @(...) ev. The update
  // event is created when the event control occurs (after n occurrences for the
  // repeat form), not immediately. ->> never blocks the issuing process, so the
  // wait happens in a spawned process.
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
        NbEventTriggerEventCoroutine(stmt, var, event_name, count, reactive,
                                     ctx, arena),
        ctx, arena);
    return StmtResult::kDone;
  }

  // Delay form (or no timing control): the update event is created when the
  // optional delay expires.
  uint64_t delay = 0;
  if (stmt->delay) delay = EvalExpr(stmt->delay, ctx, arena).ToUint64();
  auto time = ctx.CurrentTime();
  time.ticks += delay;
  ScheduleNbEventTrigger(var, event_name, time, reactive, ctx);
  return StmtResult::kDone;
}

// Rewrites any sequence name in the wait condition's read set to its synthetic
// endpoint event variable (creating that event variable on demand), so the wait
// suspends on the sequence's completion event rather than on the name itself.
static void SubstituteSequenceEndpoints(std::unordered_set<std::string>& reads,
                                        SimContext& ctx) {
  std::unordered_set<std::string> seq_adds;
  std::unordered_set<std::string> seq_removes;
  for (const auto& name : reads) {
    if (ctx.FindSequenceDecl(name)) {
      std::string ep_name = "__seq_" + name;
      auto* ep_var = ctx.FindVariable(ep_name);
      if (!ep_var) {
        ep_var = ctx.CreateVariable(ep_name, 1);
        ep_var->is_event = true;
      }
      seq_adds.insert(ep_name);
      seq_removes.insert(name);
    }
  }
  for (const auto& r : seq_removes) reads.erase(r);
  for (auto& a : seq_adds) reads.insert(a);
}

static ExecTask ExecWait(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  std::unordered_set<std::string> reads;
  CollectExprReads(stmt->condition, reads);

  SubstituteSequenceEndpoints(reads, ctx);
  std::vector<std::string_view> read_vars(reads.begin(), reads.end());
  bool suspended = false;
  while (!ctx.StopRequested()) {
    auto cond = EvalExpr(stmt->condition, ctx, arena);
    if (cond.IsTruthy()) break;
    if (read_vars.empty()) {
      if (labeled) ctx.PopStaticScope(stmt->label);
      co_return StmtResult::kDone;
    }
    suspended = true;
    co_await AnyChangeAwaiter{ctx, read_vars};
  }
  // §12.4.2.1: resuming after suspending on a wait statement is a violation
  // report flush point; drop any reports pending from before the wait.
  if (suspended) ctx.FlushPendingViolations();
  if (stmt->body) {
    auto r = co_await ExecStmt(stmt->body, ctx, arena);
    if (labeled) ctx.PopStaticScope(stmt->label);
    co_return r;
  }
  if (labeled) ctx.PopStaticScope(stmt->label);
  co_return StmtResult::kDone;
}

struct WaitOrderStepAwaiter {
  SimContext& ctx;
  const std::vector<std::string_view>& event_names;
  std::string_view triggered_name;

  bool await_ready() const noexcept { return false; }

  void await_suspend(std::coroutine_handle<> h) {
    auto done = std::make_shared<bool>(false);
    auto* out = &triggered_name;

    for (auto name : event_names) {
      auto* var = ctx.FindVariable(name);
      if (!var) continue;
      var->AddWatcher([h, name, out, done]() mutable {
        if (*done) return true;
        *done = true;
        *out = name;
        h.resume();
        return true;
      });
    }
  }

  std::string_view await_resume() const noexcept { return triggered_name; }
};

// Collects the names of the wait_order events from index `start` onward, the
// set the next step must wait on while honoring the required ordering.
static std::vector<std::string_view> RemainingWaitOrderNames(
    const std::vector<Expr*>& events, size_t start) {
  std::vector<std::string_view> remaining;
  for (size_t j = start; j < events.size(); ++j) {
    remaining.push_back(events[j]->text);
  }
  return remaining;
}

static ExecTask ExecWaitOrder(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  auto& events = stmt->wait_order_events;
  if (events.empty()) {
    if (stmt->then_branch) {
      co_return co_await ExecStmt(stmt->then_branch, ctx, arena);
    }
    co_return StmtResult::kDone;
  }

  bool failed = false;

  for (size_t i = 0; i < events.size() && !failed; ++i) {
    auto expected_name = events[i]->text;

    if (i == 0 && ctx.IsEventTriggered(expected_name)) {
      continue;
    }

    std::vector<std::string_view> remaining =
        RemainingWaitOrderNames(events, i);

    auto triggered = co_await WaitOrderStepAwaiter{ctx, remaining, {}};

    if (triggered != expected_name) {
      failed = true;
    }
  }

  if (failed) {
    if (stmt->else_branch) {
      co_return co_await ExecStmt(stmt->else_branch, ctx, arena);
    }

    // §15.5.4: when no else (fail) clause is supplied, a failed sequence
    // raises a default run-time error by calling $error (see §20.10), which
    // records ERROR severity and lets the run continue.
    EmitSeverityHeader(ctx, "ERROR", "wait_order events triggered out of order",
                       std::cerr);
    co_return StmtResult::kDone;
  }

  if (stmt->then_branch) {
    co_return co_await ExecStmt(stmt->then_branch, ctx, arena);
  }
  co_return StmtResult::kDone;
}

// Marks the just-completed fork child process finished and wakes any thread
// blocked on its await(). No-op for a process that was killed.
static void FinalizeForkChildProcess(SimContext& ctx) {
  auto* child_proc = ctx.CurrentProcess();
  if (child_proc && child_proc->sv_state != ProcessState::kKilled) {
    child_proc->sv_state = ProcessState::kFinished;
    for (auto& w : child_proc->await_waiters) {
      if (w) w.resume();
    }
    child_proc->await_waiters.clear();
  }
}

// Decrements the join/wait-fork tallies for one finished child and resumes the
// join site and/or the wait-fork waiter when their conditions are met.
static void NotifyForkChildDone(SimContext& ctx, ForkJoinState* state,
                                WaitForkState* parent_wfs,
                                Process* parent_proc) {
  state->remaining--;
  bool should_resume =
      state->join_any ? !state->resumed : (state->remaining == 0);
  if (should_resume && state->parent) {
    state->resumed = true;
    // §18.14.2: restore the spawning thread as current before the join site
    // resumes so its subsequent draws come from its own RNG, not from
    // whichever child happened to run last.
    if (state->parent_proc) ctx.SetCurrentProcess(state->parent_proc);
    state->parent.resume();
  }
  if (parent_wfs && --parent_wfs->remaining == 0 && parent_wfs->waiter) {
    ctx.SetCurrentProcess(parent_proc);
    parent_wfs->waiter.resume();
  }
}

static SimCoroutine ForkChildCoroutine(const Stmt* body, SimContext& ctx,
                                       Arena& arena, ForkJoinState* state,
                                       WaitForkState* parent_wfs,
                                       Process* parent_proc) {
  co_await ExecStmt(body, ctx, arena);

  FinalizeForkChildProcess(ctx);
  NotifyForkChildDone(ctx, state, parent_wfs, parent_proc);
}

static bool IsForkBlockItemDecl(const Stmt* s) {
  return s->kind == StmtKind::kVarDecl || s->kind == StmtKind::kBlockItemDecl;
}

// Registers the spawned child process under any named scopes it should answer
// to: a named task/function call form, a labeled block, and every named scope
// active at the fork site.
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

// Creates and schedules one fork child process for the statement s, wiring it
// into the shared join state and the spawning process's wait-fork tally.
static void SpawnForkChild(const Stmt* s, SimContext& ctx, Arena& arena,
                           ForkJoinState* state, Process* spawning_proc,
                           WaitForkState* parent_wfs, Process* parent_proc) {
  if (parent_wfs) parent_wfs->remaining++;
  auto* p = arena.Create<Process>();
  if (spawning_proc) spawning_proc->children.push_back(p);
  p->kind = ProcessKind::kInitial;
  if (spawning_proc) {
    p->is_reactive = spawning_proc->is_reactive;
    p->home_region = spawning_proc->home_region;
    p->program_block_id = spawning_proc->program_block_id;
  }
  // §18.14.2: a new thread's RNG is initialized with the next random value
  // drawn from the thread that creates it. Each child therefore receives a
  // unique seed determined solely by the parent, and the per-child seed
  // material is settled in fork order rather than execution order.
  p->rng_seed = ctx.DrawSeedForChild();
  p->coro = ForkChildCoroutine(s, ctx, arena, state, parent_wfs, parent_proc)
                .Release();

  RegisterForkChildScopes(s, p, ctx);
  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  event->callback = [p, &ctx, state, parent_wfs, parent_proc]() {
    if (!p->active) {
      state->remaining--;
      bool should_resume =
          state->join_any ? !state->resumed : (state->remaining == 0);
      if (should_resume && state->parent) {
        state->resumed = true;
        state->parent.resume();
      }
      if (parent_wfs && --parent_wfs->remaining == 0 && parent_wfs->waiter) {
        ctx.SetCurrentProcess(parent_proc);
        parent_wfs->waiter.resume();
      }
      return;
    }
    ctx.SetCurrentProcess(p);
    p->Resume();
  };
  auto fork_region = (spawning_proc && spawning_proc->is_reactive)
                         ? Region::kReactive
                         : Region::kActive;
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), fork_region, event);
}

// Spawns one fork child per non-declaration statement in the fork block, each
// wired into the shared join state and the spawning process's wait-fork tally.
static void SpawnForkChildren(const Stmt* stmt, SimContext& ctx, Arena& arena,
                              ForkJoinState* state, Process* spawning_proc,
                              WaitForkState* parent_wfs, Process* parent_proc) {
  for (auto* s : stmt->fork_stmts) {
    if (IsForkBlockItemDecl(s)) continue;
    SpawnForkChild(s, ctx, arena, state, spawning_proc, parent_wfs,
                   parent_proc);
  }
}

static ExecTask ExecFork(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  if (stmt->fork_stmts.empty()) {
    if (labeled) ctx.PopStaticScope(stmt->label);
    co_return StmtResult::kDone;
  }

  uint32_t process_count = 0;
  for (auto* s : stmt->fork_stmts) {
    if (IsForkBlockItemDecl(s)) {
      co_await ExecStmt(s, ctx, arena);
    } else {
      process_count++;
    }
  }

  if (process_count == 0) {
    if (labeled) ctx.PopStaticScope(stmt->label);
    co_return StmtResult::kDone;
  }

  auto* state = arena.Create<ForkJoinState>();
  state->remaining = process_count;
  state->join_any = (stmt->join_kind == TokenKind::kKwJoinAny);

  auto* spawning_proc = ctx.CurrentProcess();
  state->parent_proc = spawning_proc;

  // §9.6.1: wait fork blocks until every immediate child subprocess of the
  // current process has terminated, irrespective of how the child was
  // spawned. Register each child against the spawning process's wait-fork
  // tally for all join kinds, not just join_none: after join_any the
  // unblocked siblings keep running and a later wait fork must still wait on
  // them. (For plain join the count is already drained by the join site, so
  // the extra bookkeeping is inert.)
  Process* parent_proc = spawning_proc;
  WaitForkState* parent_wfs =
      parent_proc ? &parent_proc->wait_fork_state : nullptr;

  SpawnForkChildren(stmt, ctx, arena, state, spawning_proc, parent_wfs,
                    parent_proc);

  if (stmt->join_kind != TokenKind::kKwJoinNone) {
    co_await ForkJoinAwaiter{state};
  }
  if (labeled) ctx.PopStaticScope(stmt->label);
  co_return StmtResult::kDone;
}

static ExecTask ExecWaitFork(SimContext& ctx) {
  auto* proc = ctx.CurrentProcess();
  if (!proc) co_return StmtResult::kDone;
  co_await WaitForkAwaiter{&proc->wait_fork_state};
  co_return StmtResult::kDone;
}

static void RunDeferredActionSync(const Stmt* action, SimContext& ctx,
                                  Arena& arena) {
  if (!action) return;
  switch (action->kind) {
    case StmtKind::kNull:
      return;
    case StmtKind::kExprStmt:

      EvalExpr(action->expr, ctx, arena);
      return;
    case StmtKind::kBlockingAssign:

      ExecBlockingAssignImpl(action, ctx, arena);
      return;
    default:

      return;
  }
}

static void SnapshotDeferredCallArgs(const Stmt* action, SimContext& ctx,
                                     Arena& arena) {
  if (!action || action->kind != StmtKind::kExprStmt || !action->expr) return;
  if (action->expr->kind != ExprKind::kCall &&
      action->expr->kind != ExprKind::kSystemCall) {
    return;
  }
  for (auto* arg : action->expr->args) {
    if (!arg) continue;
    auto val = EvalExpr(arg, ctx, arena);
    ctx.SetDeferredArgSnapshot(arg, val);
  }
}

static void ClearDeferredCallArgSnapshots(const Stmt* action, SimContext& ctx) {
  if (!action || action->kind != StmtKind::kExprStmt || !action->expr) return;
  if (action->expr->kind != ExprKind::kCall &&
      action->expr->kind != ExprKind::kSystemCall) {
    return;
  }
  for (auto* arg : action->expr->args) {
    if (!arg) continue;
    ctx.ClearDeferredArgSnapshot(arg);
  }
}

static void ScheduleDeferredAction(const Stmt* action, bool is_final_deferred,
                                   SimContext& ctx, Arena& arena) {
  if (!action) return;

  SnapshotDeferredCallArgs(action, ctx, arena);
  Region region = is_final_deferred ? Region::kPostponed : Region::kReactive;
  auto* ev = ctx.GetScheduler().GetEventPool().Acquire();
  ev->callback = [action, &ctx, &arena]() {
    RunDeferredActionSync(action, ctx, arena);

    ClearDeferredCallArgSnapshots(action, ctx);
  };
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), region, ev);
}

// If this assertion is deferred, schedules its pass/fail action in the
// reactive/postponed region and reports true (the caller should return without
// running the action inline); otherwise reports false so the caller executes
// the action immediately.
static bool TryScheduleDeferredAssertAction(const Stmt* action,
                                            const Stmt* stmt, SimContext& ctx,
                                            Arena& arena) {
  if (!stmt->is_deferred) return false;
  ScheduleDeferredAction(action, stmt->is_final_deferred, ctx, arena);
  return true;
}

// Records a cover-immediate sampling: bumps the evaluation count and, when the
// covered expression held, the success count. No-op for assert/assume forms.
static void RecordCoverImmediateSample(const Stmt* stmt, bool is_true,
                                       SimContext& ctx) {
  if (stmt->kind != StmtKind::kCoverImmediate) return;
  ctx.IncrementCoverEvalCount();
  if (is_true) ctx.IncrementCoverSuccessCount();
}

static ExecTask ExecImmediateAssert(const Stmt* stmt, SimContext& ctx,
                                    Arena& arena) {
  auto cond = EvalExpr(stmt->assert_expr, ctx, arena);

  bool is_true = cond.IsTruthy();
  RecordCoverImmediateSample(stmt, is_true, ctx);
  if (is_true) {
    if (stmt->assert_pass_stmt) {
      if (TryScheduleDeferredAssertAction(stmt->assert_pass_stmt, stmt, ctx,
                                          arena)) {
        co_return StmtResult::kDone;
      }
      co_return co_await ExecStmt(stmt->assert_pass_stmt, ctx, arena);
    }
  } else {
    if (stmt->assert_fail_stmt) {
      if (TryScheduleDeferredAssertAction(stmt->assert_fail_stmt, stmt, ctx,
                                          arena)) {
        co_return StmtResult::kDone;
      }
      co_return co_await ExecStmt(stmt->assert_fail_stmt, ctx, arena);
    } else if (stmt->kind != StmtKind::kCoverImmediate) {
      ctx.IncrementAssertionFailCount();
      EmitSeverityHeader(ctx, "ERROR", "Assertion failed.", std::cerr);
    }
  }
  co_return StmtResult::kDone;
}

// Resolves the process targeted by a `<handle>.await()` call and validates it,
// emitting the relevant diagnostic and returning nullptr when the call does not
// resolve to a process that may legally be awaited. A non-null result is a
// process the caller should suspend on.
static Process* ResolveProcessAwaitTarget(const Expr* expr, SimContext& ctx) {
  MethodCallParts parts;
  if (!ExtractMethodCallParts(expr, parts) ||
      ctx.GetVariableClassType(parts.var_name) != "process" ||
      parts.method_name != "await") {
    return nullptr;
  }
  auto* var = ctx.FindVariable(parts.var_name);
  if (!var) return nullptr;
  auto proc_handle = var->value.ToUint64();
  auto* proc = ctx.FindProcessByHandle(proc_handle);
  if (!proc) return nullptr;
  if (proc->kind == ProcessKind::kFinal ||
      proc->kind == ProcessKind::kContAssign) {
    ctx.GetDiag().Error(
        {},
        "await() shall only target a process created by an initial "
        "procedure, always procedure, or fork block");
    return nullptr;
  }
  if (proc == ctx.CurrentProcess()) {
    ctx.GetDiag().Error({}, "process cannot await its own termination");
    return nullptr;
  }
  return proc;
}

static ExecTask ExecProcessAwait(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  (void)arena;
  auto* proc = ResolveProcessAwaitTarget(expr, ctx);
  if (proc) {
    co_await ProcessAwaitAwaiter{proc};
  }
  co_return StmtResult::kDone;
}

// Handles the system-call task forms ($cast and $stacktrace) that this
// statement may name. Returns true when the expression was one of those forms
// (and has now been fully handled); false otherwise.
static bool TryExecSystemCallTask(const Expr* expr, SimContext& ctx,
                                  Arena& arena) {
  if (!expr || expr->kind != ExprKind::kSystemCall) return false;

  // $cast invoked as a task: the evaluation performs the assignment when the
  // cast is valid and leaves the destination untouched otherwise. Unlike the
  // function form (which simply reports 0), the task form signals an invalid
  // assignment with a run-time error.
  if (expr->callee == "$cast") {
    auto result = EvalExpr(expr, ctx, arena);
    if (result.ToUint64() == 0) {
      ctx.GetDiag().Error(expr->range.start,
                          "$cast task could not assign the source expression "
                          "to the destination; assignment is invalid");
    }
    return true;
  }

  // §20.17.2: invoked as a task, $stacktrace displays the call stack of the
  // context calling it, up to the top-level process. The function form, which
  // instead returns the same text as a string, is evaluated as an expression.
  if (expr->callee == "$stacktrace") {
    std::cout << BuildStackTraceReport(ctx) << "\n";
    return true;
  }
  return false;
}

// Reports whether the expression is a `<process handle>.await()` method call.
static bool IsProcessAwaitCall(const Expr* expr, SimContext& ctx) {
  MethodCallParts parts;
  return ExtractMethodCallParts(expr, parts) &&
         ctx.GetVariableClassType(parts.var_name) == "process" &&
         parts.method_name == "await";
}

// Drops the named-scope registration and active-scope push established for a
// named task call before its body started executing.
static void UnregisterTaskNamedScope(const ModuleItem* func, SimContext& ctx) {
  ctx.PopActiveNamedScope();
  ctx.UnregisterNamedScope(func->name, ctx.CurrentProcess());
}

// Outcome of a kDisable bubbling out of a named-task body statement.
enum class InlineTaskDisable {
  kStopHere,   // the disable targeted this task; stop running its body.
  kPropagate,  // the disable targets an outer scope; unwind out of the task.
};

// Handles a kDisable result from a statement in a named/anonymous task body.
// For the self-targeted case it clears the disable target; for the propagating
// case it performs the task teardown (so the caller need only co_return).
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

static ExecTask ExecInlineTaskCall(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  auto* expr = stmt->expr;

  if (TryExecSystemCallTask(expr, ctx, arena)) {
    co_return StmtResult::kDone;
  }

  if (IsProcessAwaitCall(expr, ctx)) {
    co_return co_await ExecProcessAwait(expr, ctx, arena);
  }
  auto* func = SetupTaskCall(expr, ctx, arena);
  if (!func) {
    EvalExpr(expr, ctx, arena);
    co_return StmtResult::kDone;
  }
  bool has_name = !func->name.empty();
  if (has_name) {
    ctx.RegisterNamedScope(func->name, ctx.CurrentProcess());
    ctx.PushActiveNamedScope(func->name);
  }
  for (auto* s : func->func_body_stmts) {
    auto result = co_await ExecStmt(s, ctx, arena);
    if (result == StmtResult::kReturn) break;
    if (result == StmtResult::kDisable) {
      if (HandleInlineTaskDisable(func, expr, has_name, ctx, arena) ==
          InlineTaskDisable::kStopHere) {
        break;
      }
      co_return StmtResult::kDisable;
    }
  }
  if (has_name) UnregisterTaskNamedScope(func, ctx);
  TeardownTaskCall(func, expr, ctx, arena);
  co_return StmtResult::kDone;
}

static ExecTask ExecBlockingAssignTimed(const Stmt* stmt, SimContext& ctx,
                                        Arena& arena) {
  auto rhs_val = EvalExpr(stmt->rhs, ctx, arena);
  auto delay_val = EvalExpr(stmt->delay, ctx, arena);
  co_await DelayAwaiter{ctx, delay_val.ToUint64()};
  PerformBlockingAssign(stmt->lhs, rhs_val, ctx, arena);
  co_return StmtResult::kDone;
}

static ExecTask ExecBlockingAssignEvent(const Stmt* stmt, SimContext& ctx,
                                        Arena& arena) {
  auto rhs_val = EvalExpr(stmt->rhs, ctx, arena);
  co_await EventAwaiter{ctx, stmt->events, arena};
  PerformBlockingAssign(stmt->lhs, rhs_val, ctx, arena);
  co_return StmtResult::kDone;
}

static uint64_t EvalRepeatCount(const Expr* count_expr, SimContext& ctx,
                                Arena& arena) {
  auto val = EvalExpr(count_expr, ctx, arena);
  if (!val.IsKnown()) return 0;
  uint64_t count = val.ToUint64();
  if (val.is_signed && static_cast<int64_t>(count) <= 0) return 0;
  return count;
}

static ExecTask ExecBlockingAssignRepeatEvent(const Stmt* stmt, SimContext& ctx,
                                              Arena& arena) {
  auto rhs_val = EvalExpr(stmt->rhs, ctx, arena);
  uint64_t count = EvalRepeatCount(stmt->repeat_event_count, ctx, arena);
  if (count > 0) {
    co_await RepeatEventAwaiter{ctx, stmt->events, arena, count};
  }
  PerformBlockingAssign(stmt->lhs, rhs_val, ctx, arena);
  co_return StmtResult::kDone;
}

static SimCoroutine NbaEventCoroutine(const Stmt* stmt, Logic4Vec rhs_val,
                                      SimContext& ctx, Arena& arena) {
  co_await EventAwaiter{ctx, stmt->events, arena};
  ScheduleNonblockingAssign(stmt, rhs_val, 0, ctx, arena);
}

static SimCoroutine NbaRepeatEventCoroutine(const Stmt* stmt, Logic4Vec rhs_val,
                                            uint64_t count, SimContext& ctx,
                                            Arena& arena) {
  co_await RepeatEventAwaiter{ctx, stmt->events, arena, count};
  ScheduleNonblockingAssign(stmt, rhs_val, 0, ctx, arena);
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
  auto rhs_val = EvalExpr(stmt->rhs, ctx, arena);
  if (stmt->repeat_event_count) {
    uint64_t count = EvalRepeatCount(stmt->repeat_event_count, ctx, arena);
    if (count == 0) {
      ScheduleNonblockingAssign(stmt, rhs_val, 0, ctx, arena);
      return StmtResult::kDone;
    }
    SpawnNbaEventProcess(
        NbaRepeatEventCoroutine(stmt, rhs_val, count, ctx, arena), ctx, arena);
  } else {
    SpawnNbaEventProcess(NbaEventCoroutine(stmt, rhs_val, ctx, arena), ctx,
                         arena);
  }
  return StmtResult::kDone;
}

// Detached waiter for the event-control form of ->>: blocks (off the issuing
// process) until the event control has occurred the required number of times,
// then creates the nonblocking-region update event that fires the named event.
static SimCoroutine NbEventTriggerEventCoroutine(
    const Stmt* stmt, Variable* var, std::string_view event_name,
    uint64_t count, bool reactive, SimContext& ctx, Arena& arena) {
  for (uint64_t i = 0; i < count; ++i) {
    co_await EventAwaiter{ctx, stmt->events, arena};
  }
  ScheduleNbEventTrigger(var, event_name, ctx.CurrentTime(), reactive, ctx);
}

static StmtResult ExecDisableImpl(const Stmt* stmt, SimContext& ctx) {
  if (!stmt->expr || stmt->expr->kind != ExprKind::kIdentifier)
    return StmtResult::kDone;

  auto target = stmt->expr->text;
  if (target.empty()) return StmtResult::kDone;

  auto* current = ctx.CurrentProcess();

  auto procs = ctx.FindNamedScopeProcesses(target);
  bool self_disable = false;

  for (auto* proc : procs) {
    if (proc == current) {
      self_disable = true;
      continue;
    }

    proc->active = false;
  }

  if (self_disable) {
    ctx.SetDisableTarget(target);
    return StmtResult::kDisable;
  }

  return StmtResult::kDone;
}

static void DisableDescendants(Process* proc) {
  for (auto* child : proc->children) {
    child->active = false;
    DisableDescendants(child);
  }
}

static StmtResult ExecDisableForkImpl(SimContext& ctx) {
  auto* proc = ctx.CurrentProcess();
  if (!proc) return StmtResult::kDone;
  DisableDescendants(proc);
  proc->wait_fork_state.remaining = 0;
  proc->children.clear();
  return StmtResult::kDone;
}

// Selects the blocking-assignment execution form (timed, event/repeat-event,
// or immediate) for a kBlockingAssign statement.
static ExecTask DispatchBlockingAssign(const Stmt* stmt, SimContext& ctx,
                                       Arena& arena) {
  if (stmt->delay) return ExecBlockingAssignTimed(stmt, ctx, arena);
  if (!stmt->events.empty()) {
    if (stmt->repeat_event_count)
      return ExecBlockingAssignRepeatEvent(stmt, ctx, arena);
    return ExecBlockingAssignEvent(stmt, ctx, arena);
  }
  return ExecTask::Immediate(ExecBlockingAssignImpl(stmt, ctx, arena));
}

// Executes a kReturn statement: when inside a randsequence production with a
// return value (§18.17.7) it evaluates the expression into the production's
// return slot, then unwinds with kReturn.
static StmtResult DispatchReturn(const Stmt* stmt, SimContext& ctx,
                                 Arena& arena) {
  if (stmt->expr && ctx.RsReturnSlot() != nullptr) {
    *ctx.RsReturnSlot() =
        EvalExpr(stmt->expr, ctx, arena, ctx.RsReturnSlot()->width);
  }
  return StmtResult::kReturn;
}

ExecTask ExecStmt(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt) return ExecTask::Immediate(StmtResult::kDone);

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
    case StmtKind::kExpect:
      return ExecImmediateAssert(stmt, ctx, arena);
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
      return ExecTask::Immediate(ExecVarDeclImpl(stmt, ctx, arena));
    default:
      return ExecTask::Immediate(StmtResult::kDone);
  }
}

bool IsTimeControlStatement(StmtKind kind) {
  return kind == StmtKind::kDelay || kind == StmtKind::kEventControl;
}

}  // namespace delta
