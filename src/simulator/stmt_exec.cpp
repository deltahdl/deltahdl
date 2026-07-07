#include "simulator/stmt_exec.h"

#include <cmath>
#include <cstdint>
#include <cstring>
#include <functional>
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
#include "simulator/sva_engine.h"

namespace delta {

namespace {
// §9.6/§18.14.2: per-fork rendezvous shared by every child of one fork (join
// tally, spawning process's wait-fork tally, spawning process to restore).
struct ForkRendezvous {
  ForkJoinState* state;
  WaitForkState* parent_wfs;
  Process* parent_proc;
};
// §15.5.3: named-event trigger of the event-control form of ->> (target event
// variable, its name, required occurrence count, reactive-region flag).
struct NbEventTrigger {
  Variable* var;
  std::string_view event_name;
  uint64_t count;
  bool reactive;
};

// Flattens a named-event trigger target into a dotted name. §15.5.1's target is
// a hierarchical_event_identifier, so a member-access path (e.g. `sub.ev`) is
// joined with dots down to the same instance-qualified name the waiting process
// registered on. A leading scope prefix on a component is preserved. Returns
// false for any other target form (e.g. an array select).
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

// Resolves the trigger target to the stable name used to look up its event
// variable. A bare identifier is returned verbatim -- exactly the token the
// scope-aware FindVariable already resolves -- so this preserves the original
// resolution for every non-hierarchical case. Only a member-access path is
// flattened (and interned in the arena so the view stays valid for the deferred
// ->> scheduling and the triggered() map, both of which key by string_view).
std::string_view ResolveEventTargetName(const Expr* expr, SimContext& ctx) {
  if (!expr) return {};
  if (expr->kind == ExprKind::kIdentifier) return expr->text;
  if (expr->kind != ExprKind::kMemberAccess) return {};
  std::string name;
  if (!BuildEventTargetName(expr, name)) return {};
  auto* stored = ctx.GetArena().Create<std::string>(std::move(name));
  return *stored;
}
}  // namespace

static StmtResult ExecEventTriggerImpl(const Stmt* stmt, SimContext& ctx) {
  auto event_name = ResolveEventTargetName(stmt->expr, ctx);
  if (event_name.empty()) return StmtResult::kDone;
  auto* var = ctx.FindVariable(event_name);
  if (!var) return StmtResult::kDone;

  if (var->is_null_event) return StmtResult::kDone;

  ctx.SetEventTriggered(event_name);

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
                                                 NbEventTrigger trigger,
                                                 SimContext& ctx, Arena& arena);

static StmtResult ExecNbEventTriggerImpl(const Stmt* stmt, SimContext& ctx,
                                         Arena& arena) {
  auto event_name = ResolveEventTargetName(stmt->expr, ctx);
  if (event_name.empty()) return StmtResult::kDone;
  auto* var = ctx.FindVariable(event_name);
  if (!var) return StmtResult::kDone;

  if (var->is_null_event) return StmtResult::kDone;

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
        NbEventTriggerEventCoroutine(stmt, {var, event_name, count, reactive},
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

// Decrements the join/wait-fork tallies for one finished (or, when
// restore_parent is false, cancelled) child and resumes the join site and/or
// the wait-fork waiter when their conditions are met. §18.14.2: a normally
// completing child restores the spawning thread as current before the join site
// resumes so its subsequent draws come from its own RNG, not from whichever
// child ran last; a cancelled child never ran user code, so it does not.
static void DrainForkChild(SimContext& ctx, const ForkRendezvous& rdv,
                           bool restore_parent) {
  auto* state = rdv.state;
  state->remaining--;
  bool should_resume =
      state->join_any ? !state->resumed : (state->remaining == 0);
  if (should_resume && state->parent) {
    state->resumed = true;
    if (restore_parent && state->parent_proc)
      ctx.SetCurrentProcess(state->parent_proc);
    state->parent.resume();
  }
  if (rdv.parent_wfs && --rdv.parent_wfs->remaining == 0 &&
      rdv.parent_wfs->waiter) {
    ctx.SetCurrentProcess(rdv.parent_proc);
    rdv.parent_wfs->waiter.resume();
  }
}

// rdv is by value, not by reference: this coroutine uses rdv after the co_await
// below, but the ForkRendezvous passed in is a temporary; a reference would
// dangle in the frame, a by-value copy lives for the coroutine's duration.
static SimCoroutine ForkChildCoroutine(const Stmt* body, SimContext& ctx,
                                       Arena& arena, ForkRendezvous rdv) {
  co_await ExecStmt(body, ctx, arena);

  FinalizeForkChildProcess(ctx);
  DrainForkChild(ctx, rdv, /*restore_parent=*/true);
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

// Allocates the child Process and copies the spawning process's execution
// context (region/reactivity/program-block) and a freshly drawn per-child RNG
// seed onto it, then links it into the spawning process's child list.
static Process* CreateForkChildProcess(SimContext& ctx, Arena& arena,
                                       Process* spawning_proc) {
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
  return p;
}

// Builds the scheduler callback that starts (or, if cancelled e.g. by disable
// fork, drains the tallies for) one fork child process when its start event
// fires.
static std::function<void()> MakeForkChildStartCallback(
    Process* p, SimContext& ctx, const ForkRendezvous& rdv) {
  return [p, &ctx, rdv]() {
    if (!p->active) {
      DrainForkChild(ctx, rdv, /*restore_parent=*/false);
      return;
    }
    ctx.SetCurrentProcess(p);
    p->Resume();
  };
}

// Creates and schedules one fork child process for the statement s, wiring it
// into the shared join state and the spawning process's wait-fork tally.
static void SpawnForkChild(const Stmt* s, SimContext& ctx, Arena& arena,
                           Process* spawning_proc, const ForkRendezvous& rdv) {
  if (rdv.parent_wfs) rdv.parent_wfs->remaining++;
  auto* p = CreateForkChildProcess(ctx, arena, spawning_proc);
  p->coro = ForkChildCoroutine(s, ctx, arena, rdv).Release();

  RegisterForkChildScopes(s, p, ctx);
  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  event->callback = MakeForkChildStartCallback(p, ctx, rdv);
  auto fork_region = (spawning_proc && spawning_proc->is_reactive)
                         ? Region::kReactive
                         : Region::kActive;
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), fork_region, event);
}

// Spawns one fork child per non-declaration statement in the fork block, each
// wired into the shared join state and the spawning process's wait-fork tally.
static void SpawnForkChildren(const Stmt* stmt, SimContext& ctx, Arena& arena,
                              Process* spawning_proc,
                              const ForkRendezvous& rdv) {
  for (auto* s : stmt->fork_stmts) {
    if (IsForkBlockItemDecl(s)) continue;
    SpawnForkChild(s, ctx, arena, spawning_proc, rdv);
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

  SpawnForkChildren(stmt, ctx, arena, spawning_proc,
                    {state, parent_wfs, parent_proc});

  if (stmt->join_kind != TokenKind::kKwJoinNone) {
    co_await ForkJoinAwaiter{state};
  }
  if (labeled) ctx.PopStaticScope(stmt->label);
  co_return StmtResult::kDone;
}

// §13.4.4: a function body must not block, so it may spawn background processes
// only through fork...join_none. This performs the same child-process spawning
// as ExecFork's join_none path, but as a plain call with no coroutine await, so
// the synchronous function-body executor (ExecFuncStmt) can run it. A fork with
// any other join kind inside a function is illegal (it would block) and is left
// untouched here.
void SpawnForkJoinNone(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt || stmt->join_kind != TokenKind::kKwJoinNone) return;
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);

  uint32_t process_count = 0;
  for (auto* s : stmt->fork_stmts) {
    if (!IsForkBlockItemDecl(s)) process_count++;
  }
  if (process_count == 0) {
    if (labeled) ctx.PopStaticScope(stmt->label);
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
  if (labeled) ctx.PopStaticScope(stmt->label);
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

// §16.4.4: reports whether a pending deferred report has been individually
// cancelled by a `disable <assertion_label>` statement in its process (see
// Process::cancelled_deferred_labels). An unlabeled assertion cannot be named
// by a disable, so an empty label is never cancelled.
static bool DeferredReportCancelled(const Process* proc,
                                    const std::string& label) {
  return proc && !label.empty() &&
         proc->cancelled_deferred_labels.count(label) != 0;
}

static void ScheduleDeferredAction(const Stmt* action, bool is_final_deferred,
                                   std::string_view assertion_label,
                                   SimContext& ctx, Arena& arena) {
  if (!action) return;

  SnapshotDeferredCallArgs(action, ctx, arena);
  Region region = is_final_deferred ? Region::kPostponed : Region::kReactive;
  // §16.4.2: the report is pending until its region runs. Capture the process
  // and its report generation now; if a flush point bumps the generation before
  // the region fires (e.g. the process resumes or an always_comb re-triggers in
  // the same time step), the queued report has been flushed and is skipped.
  Process* proc = ctx.CurrentProcess();
  uint64_t gen = ctx.CurrentDeferredReportGeneration();
  // §16.4.4: also remember which assertion queued this report, so a later
  // `disable <that label>` in the same process can cancel just this report.
  std::string label(assertion_label);
  auto* ev = ctx.GetScheduler().GetEventPool().Acquire();
  ev->callback = [action, proc, gen, label, &ctx, &arena]() {
    if ((!proc || proc->deferred_report_generation == gen) &&
        !DeferredReportCancelled(proc, label)) {
      RunDeferredActionSync(action, ctx, arena);
    }
    ClearDeferredCallArgSnapshots(action, ctx);
  };
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), region, ev);
}

// §16.4.1: when a deferred assertion fails with no else clause, its default
// $error report is a pending assertion report rather than an immediate one.
// Like the action-block subroutine call, it is not emitted where the assertion
// is processed; it is deferred and executed with the rest of the process's
// pending reports -- in the Reactive region for an observed (#0) deferred
// assertion, or in the Postponed region for a final deferred assertion.
static void ScheduleDeferredSeverityReport(bool is_final_deferred,
                                           std::string_view assertion_label,
                                           SimContext& ctx) {
  Region region = is_final_deferred ? Region::kPostponed : Region::kReactive;
  // §16.4.2: the default $error is a pending report too, so it is flushed the
  // same way when the process reaches a flush point before its region runs.
  Process* proc = ctx.CurrentProcess();
  uint64_t gen = ctx.CurrentDeferredReportGeneration();
  // §16.4.4: the default $error is cancellable by a specific-assertion disable
  // just like an action-block report; carry the assertion's label to check.
  std::string label(assertion_label);
  auto* ev = ctx.GetScheduler().GetEventPool().Acquire();
  ev->callback = [proc, gen, label, &ctx]() {
    if (proc && proc->deferred_report_generation != gen) return;
    if (DeferredReportCancelled(proc, label)) return;
    EmitSeverityHeader(ctx, "ERROR", "Assertion failed.", std::cerr);
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
  ScheduleDeferredAction(action, stmt->is_final_deferred, stmt->label, ctx,
                         arena);
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

// §20.11: the Table 20-6 assertion_type bit that identifies an immediate
// assertion statement -- simple immediate, observed deferred, or final deferred
// -- so a $assertcontrol assertion_type mask can select whether it is checked.
static uint32_t ImmediateAssertionTypeBit(const Stmt* stmt) {
  if (!stmt->is_deferred) {
    return static_cast<uint32_t>(AssertionTypeBit::kSimpleImmediate);
  }
  return stmt->is_final_deferred
             ? static_cast<uint32_t>(AssertionTypeBit::kFinalDeferredImmediate)
             : static_cast<uint32_t>(
                   AssertionTypeBit::kObservedDeferredImmediate);
}

// §20.11: the Table 20-7 directive_type bit for an immediate assertion -- an
// assert, cover, or assume directive -- used the same way against a
// $assertcontrol directive_type mask.
static uint32_t ImmediateDirectiveTypeBit(const Stmt* stmt) {
  switch (stmt->kind) {
    case StmtKind::kCoverImmediate:
      return static_cast<uint32_t>(DirectiveTypeBit::kCover);
    case StmtKind::kAssumeImmediate:
      return static_cast<uint32_t>(DirectiveTypeBit::kAssume);
    default:
      return static_cast<uint32_t>(DirectiveTypeBit::kAssert);
  }
}

static ExecTask ExecImmediateAssert(const Stmt* stmt, SimContext& ctx,
                                    Arena& arena) {
  // §16.3 / §20.11: the execution of immediate assertions can be controlled by
  // the assertion control system tasks. When $assertcontrol Off/Kill (or
  // $assertoff/$assertkill) has stopped checking for this assertion's type and
  // directive, the assertion is not evaluated, records nothing, and runs no
  // action on this activation.
  uint32_t type_bit = ImmediateAssertionTypeBit(stmt);
  uint32_t directive_bit = ImmediateDirectiveTypeBit(stmt);
  if (!ctx.AssertCheckingEnabled(type_bit, directive_bit)) {
    co_return StmtResult::kDone;
  }

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
      // §20.11: the fail-action controls do not affect the statistics counters,
      // so the failure is still counted even when its report is suppressed.
      ctx.IncrementAssertionFailCount();
      // §16.3 / §20.11: with no else clause the tool reports the violation via
      // $error, unless $assertcontrol FailOff ($assertfailoff) has suppressed
      // the fail action for this assertion's type and directive.
      if (ctx.AssertFailActionEnabled(type_bit, directive_bit)) {
        // §16.4.1: for a deferred assertion this default report is a pending
        // report, scheduled with the process's other deferred reports rather
        // than emitted here; a simple immediate assertion reports at once.
        if (stmt->is_deferred) {
          ScheduleDeferredSeverityReport(stmt->is_final_deferred, stmt->label,
                                         ctx);
        } else {
          EmitSeverityHeader(ctx, "ERROR", "Assertion failed.", std::cerr);
        }
      }
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
enum class InlineTaskDisable : std::uint8_t {
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
  // §10.4.1 intra-assignment delay is a §9.4.1 delay control: normalize the
  // delay value with the shared rules (unknown/high-Z -> zero, negative ->
  // time-variable-width unsigned) rather than taking the raw bits.
  co_await DelayAwaiter{ctx, DelayTicksFromValue(delay_val)};
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
  // §9.4.5: a repeat count <= 0 behaves as if there were no repeat construct.
  // A negative signed value narrower than 64 bits arrives zero-extended from
  // ToUint64(), so sign-extend it before the signed comparison or e.g. a 32-bit
  // -3 would read as a large positive count instead of bypassing the repeat.
  if (val.is_signed && val.width > 0 && val.width < 64) {
    uint64_t sign_bit = uint64_t{1} << (val.width - 1);
    if (count & sign_bit) {
      uint64_t mask = (uint64_t{1} << val.width) - 1;
      count = count | ~mask;
    }
  }
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
// trigger is by value, not by reference: it is used after the co_await
// suspensions below, but the NbEventTrigger passed in is a temporary; a
// by-value copy lives in the coroutine frame, a reference would dangle.
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
    // §16.4.4: applying a disable to the outermost scope of another procedure
    // that has an active deferred assertion queue flushes that queue -- every
    // pending (not-yet-matured) deferred immediate assertion report on it is
    // cleared, in addition to the normal disable activities of §9.6.2. A
    // pending report's scheduled Reactive/Postponed event is gated only on the
    // process's deferred report generation (not on its active flag), so bumping
    // that generation invalidates the reports this process queued earlier in
    // the time step, mirroring FlushPendingDeferredReports for the disabled
    // process (see §16.4.2). Reports that already matured have run and are
    // unaffected.
    proc->deferred_report_generation++;
  }

  if (self_disable) {
    ctx.SetDisableTarget(target);
    return StmtResult::kDisable;
  }

  // §16.4.4: a `disable <label>` that names no block, task, or process scope
  // may instead name a specific deferred immediate assertion. Such a disable
  // cancels only that assertion's still-pending reports and does not unwind the
  // process (unlike disabling a scope). Record the label on the current
  // process; each pending report queued by that assertion skips execution when
  // its region runs (see ScheduleDeferredAction /
  // ScheduleDeferredSeverityReport). Reports of other assertions, and any
  // report that has already matured, are untouched.
  if (procs.empty() && current) {
    current->cancelled_deferred_labels.insert(std::string(target));
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
