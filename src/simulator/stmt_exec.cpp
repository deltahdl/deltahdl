#include "simulator/stmt_exec.h"

#include <cstdint>
#include <cstring>
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
#include "simulator/covergroup_instance.h"
#include "simulator/eval_call_result.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_instance_task.h"
#include "simulator/eval_mailbox.h"
#include "simulator/eval_semaphore.h"
#include "simulator/evaluation.h"
#include "simulator/exec_task.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/stmt_exec_internal.h"
#include "simulator/stmt_result.h"

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

// The stable name a trigger target's event variable is looked up by: a bare
// identifier as written, the token the scope-aware FindVariable resolves, and
// a member-access path flattened and interned in the arena so the view holds
// for the deferred ->> scheduling and the triggered() map, both string_view
// keyed.
std::string_view ResolveEventTargetName(const Expr* expr, SimContext& ctx) {
  if (!expr) return {};
  if (expr->kind == ExprKind::kIdentifier) return expr->text;
  if (expr->kind != ExprKind::kMemberAccess) return {};
  std::string name;
  // §23.6 with §27.4: a path through a loop generate block instance,
  // `g[1].e`, selects the instance by a literal index, which the hierarchical
  // name spells as the waiting process's lookup does
  // (HierarchicalReferenceName).
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
  // §15.5.3: the event itself records the step, which a class's event
  // property, found by no name, is read by (TryClassEventTriggered).
  var->triggered_ticks = ctx.CurrentTime().ticks;

  auto pending = std::move(var->watchers);
  var->watchers.clear();
  auto& sched = ctx.GetScheduler();
  auto region = ctx.IsReactiveContext() ? Region::kReactive : Region::kActive;
  // A watcher answers false when this trigger does not wake it -- its process
  // is suspended (§9.7) or its `iff` does not hold (§9.4.2.3) -- and it stays
  // armed for the next trigger, as Variable::NotifyWatchers keeps it.
  for (auto& cb : pending) {
    auto* event = sched.GetEventPool().Acquire();
    event->callback = [var, cb = std::move(cb)]() mutable {
      if (!cb()) var->AddWatcher(std::move(cb));
    };
    sched.ScheduleEvent(ctx.CurrentTime(), region, event);
  }
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

  // Event-control form, ->> @(...) ev or ->> repeat(n) @(...) ev: the update
  // event is created when the control occurs (after n occurrences for repeat),
  // and ->> never blocks the issuer, so the wait happens in a spawned process.
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

  // Delay form, or none: the update event is created when the delay expires.
  uint64_t delay = 0;
  if (stmt->delay) {
    delay = DelayValueToTicks(EvalExpr(stmt->delay, ctx, arena), ctx);
  }
  auto time = ctx.CurrentTime();
  time.ticks += delay;
  ScheduleNbEventTrigger(var, event_name, time, reactive, ctx);
  return StmtResult::kDone;
}

// Marks the just-completed fork child process finished and wakes any thread
// blocked on its await(). No-op for a process that was killed.
static void FinalizeForkChildProcess(SimContext& ctx) {
  if (auto* child_proc = ctx.CurrentProcess()) child_proc->Finish();
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

// Allocates the child Process, copies the spawning process's execution context
// (region, reactivity, program block, carried stacks) and a fresh RNG seed onto
// it, and links it into the spawning process's child list.
static Process* CreateForkChildProcess(SimContext& ctx, Arena& arena,
                                       Process* spawning_proc) {
  auto* p = arena.Create<Process>();
  if (spawning_proc) spawning_proc->children.push_back(p);
  p->kind = ProcessKind::kInitial;
  if (spawning_proc) {
    p->is_reactive = spawning_proc->is_reactive;
    p->home_region = spawning_proc->home_region;
    p->program_block_id = spawning_proc->program_block_id;
    // §9.3.2 with §23.9 and §27.4: a branch's statements are statements of
    // the scope the fork stands in, so its names resolve in the same module
    // instance and generate block instances. Left at the defaults, a branch
    // in a submodule or a program read and triggered the top's names, and
    // `-> e` there woke no process waiting on the instance's e.
    p->inst_prefix = spawning_proc->inst_prefix;
    p->gen_prefixes = spawning_proc->gen_prefixes;
    p->gen_block_name = spawning_proc->gen_block_name;
  }
  ctx.CopyCarriedStacksTo(*p);
  // §18.14.2: a new thread's RNG is seeded with the next random value drawn
  // from the thread that creates it, so each child's seed is the parent's
  // alone and settled in fork order rather than execution order.
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

// The join of a fork, awaited as a statement of its own so that a disable
// taking the parent out of it (TryUnwindForDisable) lands in ExecFork, which
// then closes the fork's scope.
static ExecTask AwaitForkJoin(ForkJoinState* state) {
  co_await ForkJoinAwaiter{state};
  co_return StmtResult::kDone;
}

// §9.3.5 with §9.6.2: a fork's label names a block a disable can end, from one
// of its own branches or from another process. The label is a named scope of
// the spawning process for as long as it waits at the join, and of every
// branch (RegisterForkChildScopes), so the disable kills the branches and
// takes the parent out of the join, which then completes at once. §19.3: the
// block beginning and ending are block events a covergroup may sample at, the
// ending only where the block was not disabled.
static void EnterForkLabelScope(const Stmt* stmt, SimContext& ctx,
                                Arena& arena) {
  ctx.PushStaticScope(stmt->label);
  ctx.PushActiveNamedScope(stmt->label);
  ctx.RegisterNamedScope(stmt->label, ctx.CurrentProcess());
  SampleAtBlockEvent(stmt->label, true, ctx, arena);
}

static void ExitForkLabelScope(const Stmt* stmt, SimContext& ctx, Arena& arena,
                               bool ended) {
  if (ended) SampleAtBlockEvent(stmt->label, false, ctx, arena);
  ctx.UnregisterNamedScope(stmt->label, ctx.CurrentProcess());
  ctx.PopActiveNamedScope();
  ctx.PopStaticScope(stmt->label);
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

    // §9.6.1: wait fork blocks until every immediate child subprocess of the
    // current process has terminated, however the child was spawned. Each
    // child is registered against the spawning process's wait-fork tally for
    // every join kind, not join_none alone: after join_any the unblocked
    // siblings keep running and a later wait fork must still wait on them, and
    // for plain join the count is drained by the join site, so the
    // bookkeeping is inert.
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

// §13.4.4: a function body must not block, so it spawns background processes
// through fork...join_none alone; the same spawning as ExecFork's join_none
// path, as a plain call with no await, for the synchronous function-body
// executor (ExecFuncStmt). Any other join kind inside a function is illegal
// and is left untouched.
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

// The statements of the task `func` enabled by `expr`, run in turn until one
// returns, or until a disable reaches it: §9.6.2 ends the task's activation at
// a disable of its own name, which HandleInlineTaskDisable answers kStopHere
// for, and passes any other disable on as kDisable for the caller to unwind.
// §19.3: the task ending is a block event a covergroup may sample at, unless
// the task was disabled.
static ExecTask ExecInlineTaskBody(const ModuleItem* func, const Expr* expr,
                                   SimContext& ctx, Arena& arena) {
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
    // §20.2: no statement of the process runs after a $finish, nor after a
    // $stop, as a sequential block's own statements do not.
    if (ctx.StopRequested()) co_return StmtResult::kDone;
  }
  if (has_name) SampleAtBlockEvent(func->name, false, ctx, arena);
  co_return StmtResult::kDone;
}

// Runs at once a call statement served before any search for a task to
// enable: a system task call, or a call of rand_mode() or constraint_mode();
// false where the statement is neither.
static bool ExecNonSuspendingCall(const Expr* expr, SimContext& ctx,
                                  Arena& arena) {
  if (TryExecSystemCallTask(expr, ctx, arena)) return true;
  // §18.8 and §18.9: rand_mode() and constraint_mode() are neither tasks nor
  // waits, so the expression evaluator runs them at once. §11.3.1 has their
  // receiver evaluated once, and the checks in ExecInlineTaskCall evaluate a
  // receiver such as `pk().x` to learn whether it is a process, a semaphore or
  // a mailbox.
  if (!IsModeMethodCall(expr)) return false;
  ExecCallStmtExpr(expr, ctx, arena);
  return true;
}

// The calls a statement makes its process wait in, which only a statement
// can: a process's await() or suspend() (§9.7), a semaphore's get() (§15.3)
// and a mailbox's put(), get() or peek() (§15.4).
enum class WaitingCall : std::uint8_t { kNone, kProcess, kSemaphore, kMailbox };

static WaitingCall ClassifyWaitingCall(const Expr* expr, SimContext& ctx,
                                       Arena& arena) {
  if (IsSuspendingProcessCall(expr, ctx, arena)) return WaitingCall::kProcess;
  if (SemaphoreCallTarget(expr, ctx, "get") != nullptr)
    return WaitingCall::kSemaphore;
  if (IsMailboxBlockingCall(expr, ctx, arena)) return WaitingCall::kMailbox;
  return WaitingCall::kNone;
}

// §11.3.1: the receiver `held` holds, if any, is released once the object the
// call waits on is resolved, before the process waits.
static ExecTask ExecWaitingCall(WaitingCall kind, const Expr* expr,
                                CallResultReceiverScope& held, SimContext& ctx,
                                Arena& arena) {
  if (kind == WaitingCall::kProcess) {
    co_return co_await ExecSuspendingProcessCall(expr, ctx, arena, held);
  }
  // §15.4.3, §15.4.5 and §15.4.7: put(), get() and peek() wait on the mailbox.
  if (kind == WaitingCall::kMailbox) {
    co_return co_await ExecMailboxCall(expr, ctx, arena, held);
  }
  // §15.3: a process calling get() procures the keys it asks for before it can
  // continue, and waits where it stands until enough keys are in the bucket.
  // The wait is why this is served here and put()/try_get() are served by the
  // expression evaluator: only a statement can suspend the process it is in.
  auto* sem = SemaphoreCallTarget(expr, ctx, "get");
  int32_t count = SemaphoreKeyArg(expr, ctx, arena, 1);
  held.Release();
  // §15.3.3: a negative count is an error, and the process does not wait.
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

  // §8.6 with §11.3.1: a receiver that starts at a call, `pk().t()`,
  // `pk().kid.f()` or `pk().a[1].f()`, is evaluated once and held
  // (CallResultReceiverScope) while the statement is asked whether it is a
  // wait, then a task to enable through the object (§13.3), each question
  // evaluating the receiver; a statement that is neither is run by the
  // expression evaluator while the value is still held. The value is released
  // before the process waits or a task's body runs, since another process may
  // reach the statement meanwhile.
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
  // §13.3 with §8.6: a task enabled through an object handle runs as a
  // coroutine too, so its timing controls suspend this process.
  if (enables_task) {
    co_return co_await ExecInstanceTaskCall(instance_call, expr, ctx, arena);
  }
  auto* func = ctx.EnterSubroutinePackage(SetupTaskCall(expr, ctx, arena));
  if (!func) {
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
  auto rhs_val = EvalExpr(stmt->rhs, ctx, arena);
  auto delay_val = EvalExpr(stmt->delay, ctx, arena);
  // §10.4.1's intra-assignment delay is a §9.4.1 delay control: the value is
  // normalized by the shared rules (unknown or high-Z to zero, negative to the
  // time variable's unsigned width) and rounded to §3.14.1's precision.
  co_await DelayAwaiter{ctx, DelayValueToTicks(delay_val, ctx)};
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

static SimCoroutine NbaEventCoroutine(const Stmt* stmt, NbaSample rhs_val,
                                      SimContext& ctx, Arena& arena) {
  co_await EventAwaiter{ctx, stmt->events, arena};
  ScheduleNonblockingAssign(stmt, rhs_val, 0, ctx, arena);
}

static SimCoroutine NbaRepeatEventCoroutine(const Stmt* stmt, NbaSample rhs_val,
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
  // §10.4.2 (printed page 253): the right-hand side is evaluated when the
  // statement executes, and the event control only defers the update, so the
  // sample is the one the undeferred statement takes -- copied into the arena
  // (§4.9.4, SampleNbaRhs) as it is held across the widest gap between
  // sampling and update in the simulator, and carrying the tag a tagged union
  // target's update sets (§7.3.2, printed 151), which the vector never holds:
  // `u <= @(e) tagged Valid 5` landed the bits alone, so `u.Other` raised
  // nothing after the event.
  NbaSample rhs_val = SampleNonblockingRhs(stmt, ctx, arena);
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
  return ExecTask::Immediate(ExecImmediateBlockingAssign(stmt, ctx, arena));
}

// Executes a kReturn statement: when inside a randsequence production with a
// return value (§18.17.7) it evaluates the expression into the production's
// return slot, then unwinds with kReturn.
//
// §18.17.7 gives the production's implicit variable "the return type of the
// production", so a return is an assignment to an object of that type and not
// a replacement of it, exactly as §13.4.1 makes a function's return one. §10.7
// then truncates or extends the expression to the object's width. Handing the
// width to EvalExpr as a context width does not do this on its own: a sized
// literal is self-determined, so `return 8'hFF` from a production returning a
// four-bit typedef name came back eight bits wide and replaced the slot the
// declared width had sized, and the implicit variable read 255 where the type
// says 15. ExecFuncReturn resizes for the same reason.
//
// A slot of zero width is a string production's (§6.16), which has no declared
// width for the value to be resized to; ResizeToWidth leaves that value alone.
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

// Dispatch on statement kind. Label handling for non-block statements lives in
// ExecStmt; begin/end and fork blocks manage their own label scope.
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

// §21.2.1.5: a statement label is a hierarchy level of its own, so a system
// task invoked under the labeled statement reports the label in %m. The label
// scope is active only while the statement runs; it is popped on every exit
// path, including a propagating disable.
//
// §9.3.5 with §9.6.2: the label also makes the statement one a disable can
// name, from within it or from another process, as a named block is; the
// disable ends the statement and control goes on after it.
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

bool CurrentProcessEnded(const SimContext& ctx) {
  const Process* cur = ctx.CurrentProcess();
  return cur != nullptr && !cur->active;
}

bool ProcessGoesOn(const SimContext& ctx) {
  return !ctx.StopRequested() && !CurrentProcessEnded(ctx);
}

ExecTask ExecStmt(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt || CurrentProcessEnded(ctx)) {
    return ExecTask::Immediate(StmtResult::kDone);
  }
  // Named begin/end and fork blocks push their own label scope (ExecBlock /
  // ExecFork); every other labeled statement gets the scope wrapper here.
  if (!stmt->label.empty() && stmt->kind != StmtKind::kBlock &&
      stmt->kind != StmtKind::kFork) {
    return ExecLabeledStmt(stmt, ctx, arena);
  }
  return ExecStmtDispatch(stmt, ctx, arena);
}

bool IsTimeControlStatement(StmtKind kind) {
  return kind == StmtKind::kDelay || kind == StmtKind::kEventControl;
}

}  // namespace delta
