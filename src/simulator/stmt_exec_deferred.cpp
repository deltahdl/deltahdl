#include <cmath>
#include <coroutine>
#include <cstdint>
#include <cstring>
#include <functional>
#include <iostream>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "elaborator/global_clocking_sampled_value.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/awaiters_event_control.h"
#include "simulator/evaluation.h"
#include "simulator/expr_walk.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/scope_hier_name.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_exec_internal.h"
#include "simulator/sva_engine.h"
#include "simulator/sva_engine_sampling.h"

namespace delta {

static void RunDeferredActionSync(const Stmt* action, SimContext& ctx,
                                  Arena& arena) {
  if (!action) return;
  switch (action->kind) {
    case StmtKind::kNull:
      return;
    case StmtKind::kExprStmt:

      if (!TryExecSystemCallTask(action->expr, ctx, arena)) {
        EvalExpr(action->expr, ctx, arena);
      }
      return;
    case StmtKind::kBlockingAssign:

      ExecBlockingAssignImpl(action, ctx, arena);
      return;
    default:

      return;
  }
}

// §16.4: an actual argument passed by value to the action's subroutine,
// function calls included, is fully evaluated at the instant the deferred
// assertion's expression is evaluated, not when the call runs in its region.
// The values are evaluated here, where the assertion is processed, and
// returned to the caller to carry in the report's event: each pending report
// keeps its own, because one statement processed several times in a time step
// -- in a loop, say -- queues one report per pass, each owing the actuals of
// the pass that queued it, and a store keyed by the expression alone would hold
// only the last pass's values for all of them. The values are installed in the
// context for the length of the call and removed after it, so an argument
// expression evaluated inside the call answers with its snapshot rather than
// the value then current. A pass-by-reference actual is aliased to its
// variable when the call binds it, so a snapshot of it goes unread, and the
// call reads the value the variable holds in the Reactive or Postponed region
// as §16.4 has it.
using DeferredArgSnapshots = std::vector<std::pair<const Expr*, Logic4Vec>>;

static DeferredArgSnapshots SnapshotDeferredCallArgs(const Stmt* action,
                                                     SimContext& ctx,
                                                     Arena& arena) {
  DeferredArgSnapshots snaps;
  const Expr* call = SubroutineCallOfStmt(action);
  if (call == nullptr) return snaps;
  for (auto* arg : call->args) {
    if (!arg) continue;
    snaps.emplace_back(arg, EvalExpr(arg, ctx, arena));
  }
  return snaps;
}

static void RunDeferredActionWithSnapshots(const Stmt* action,
                                           const DeferredArgSnapshots& snaps,
                                           SimContext& ctx, Arena& arena) {
  for (const auto& snap : snaps)
    ctx.SetDeferredArgSnapshot(snap.first, snap.second);
  RunDeferredActionSync(action, ctx, arena);
  for (const auto& snap : snaps) ctx.ClearDeferredArgSnapshot(snap.first);
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

// §16.4.1: a pending assertion report is placed in the queue of the process
// executing the assertion, and §20.10 has its severity message and §21.2.1.5
// its %m name the hierarchical scope of the statement, which the labels the
// process stands inside are part of. The report's event runs after the process
// has moved on or suspended, with the context holding whatever ran last, so
// the process and its named scopes are recorded when the report is queued and
// stood back up around the report, then put back as they were.
struct PendingReportScope {
  Process* proc = nullptr;
  std::vector<std::string_view> named_scopes;

  static PendingReportScope Capture(const SimContext& ctx) {
    return {ctx.CurrentProcess(), ctx.ActiveNamedScopes()};
  }

  void Install(SimContext& ctx, PendingReportScope& saved) const {
    saved = Capture(ctx);
    Swap(ctx, *this);
  }

  static void Swap(SimContext& ctx, const PendingReportScope& to) {
    ctx.SetCurrentProcess(to.proc);
    while (!ctx.ActiveNamedScopes().empty()) ctx.PopActiveNamedScope();
    for (std::string_view scope : to.named_scopes) {
      ctx.PushActiveNamedScope(scope);
    }
  }
};

// §16.4.1 and §16.4.2: queues one pending assertion report -- an action
// block's subroutine call, the default $error, or a deferred cover's result --
// in the Reactive region for an observed deferred assertion and the Postponed
// region for a final one, where `run` executes it. The process and its report
// generation are captured now; if a flush point bumps the generation before
// the region fires (the process resumes, or an always_comb re-triggers in the
// same time step), the queued report has been flushed and is skipped, as it
// is when §16.4.4's `disable <assertion_label>` has cancelled it.
static void SchedulePendingReport(bool is_final_deferred,
                                  std::string_view assertion_label,
                                  SimContext& ctx, std::function<void()> run) {
  Region region = is_final_deferred ? Region::kPostponed : Region::kReactive;
  PendingReportScope scope = PendingReportScope::Capture(ctx);
  uint64_t gen = ctx.CurrentDeferredReportGeneration();
  std::string label(assertion_label);
  auto* ev = ctx.GetScheduler().GetEventPool().Acquire();
  ev->callback = [scope, gen, label, run = std::move(run), &ctx]() {
    if (scope.proc && scope.proc->deferred_report_generation != gen) return;
    if (DeferredReportCancelled(scope.proc, label)) return;
    PendingReportScope saved;
    scope.Install(ctx, saved);
    run();
    PendingReportScope::Swap(ctx, saved);
  };
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), region, ev);
}

static void ScheduleDeferredAction(const Stmt* action, bool is_final_deferred,
                                   std::string_view assertion_label,
                                   SimContext& ctx, Arena& arena) {
  if (!action) return;
  DeferredArgSnapshots snaps = SnapshotDeferredCallArgs(action, ctx, arena);
  SchedulePendingReport(is_final_deferred, assertion_label, ctx,
                        [action, snaps = std::move(snaps), &ctx, &arena]() {
                          RunDeferredActionWithSnapshots(action, snaps, ctx,
                                                         arena);
                        });
}

// §16.4.1: when a deferred assertion fails with no else clause, its default
// $error report is a pending assertion report rather than an immediate one.
// Like the action-block subroutine call, it is not emitted where the assertion
// is processed; it is deferred and executed with the rest of the process's
// pending reports.
static void ScheduleDeferredSeverityReport(bool is_final_deferred,
                                           std::string_view assertion_label,
                                           uint32_t line, SimContext& ctx) {
  SchedulePendingReport(
      is_final_deferred, assertion_label, ctx, [line, &ctx]() {
        EmitSeverityHeader(ctx, "ERROR", "Assertion failed.", std::cerr, line);
      });
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

// §4.4.2.6: "The code specified by blocking assignments in checkers, program
// blocks and the code in action blocks of concurrent assertions are scheduled
// in the Reactive region", which §4.4.2.5 states again from the property's
// side: "During property evaluation, pass/fail code shall be scheduled in the
// Reactive region of the current time slot." The action therefore does not run
// where the property was evaluated, and §4.4's region order is what that buys:
// the design's Active-region code has settled before a testbench reacts to the
// assertion, so nothing the action writes can be read by the design in the same
// time slot.
//
// The action runs in a process of its own rather than from a plain callback
// because it is ordinary procedural code: it may be a begin/end block and it
// may carry a delay, and §16.14.5 has the assertion that queued it back at its
// clocking event for the next tick whatever the action does. Running it inline
// from a Reactive-region callback would put the region right and leave a
// delayed action stalling the assertion that queued it.
static SimCoroutine ConcurrentAssertActionCoroutine(const Stmt* action,
                                                    SimContext& ctx,
                                                    Arena& arena) {
  co_await ExecStmt(action, ctx, arena);
}

// A process a concurrent assertion hands part of an attempt to: its action
// block (§4.4.2.6), or the attempt itself where §16.9.4 answers it at a later
// tick. §23.6 resolves the names it writes under the instance and generate
// prefixes the assertion stands in, so the process carries the ones the
// process that reached the assertion had.
static Process* CreateAssertionChildProcess(SimContext& ctx, Arena& arena,
                                            Region home_region) {
  auto* p = arena.Create<Process>();
  p->kind = ProcessKind::kInitial;
  p->home_region = home_region;
  if (auto* asserting = ctx.CurrentProcess()) {
    p->inst_prefix = asserting->inst_prefix;
    p->gen_prefixes = asserting->gen_prefixes;
    p->program_block_id = asserting->program_block_id;
  }
  // §18.14.2: a new thread's RNG is seeded with the next value drawn from the
  // thread that creates it, so an action block that randomizes draws from its
  // own stream and does so reproducibly.
  p->rng_seed = ctx.DrawSeedForChild();
  return p;
}

// Starts the process at the current time in `region`, where its coroutine runs
// to its first wait. A process disabled before that is left where it is.
static void ScheduleAssertionChildStart(Process* p, Region region,
                                        SimContext& ctx) {
  auto* ev = ctx.GetScheduler().GetEventPool().Acquire();
  ev->callback = [p, &ctx]() {
    if (!p->active) return;
    ctx.SetCurrentProcess(p);
    p->Resume();
  };
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), region, ev);
}

// Schedules a concurrent assertion's action block into the region §4.4.2.6
// gives it and reports whether it did, so a caller that gets false runs the
// action where it stands. An immediate assertion's action block is that case:
// §16.3 executes it in the procedure that reached the assert, so only a
// statement carrying a concurrent assertion's property takes this path.
static bool TryScheduleConcurrentAssertAction(const Stmt* action,
                                              const Stmt* stmt, SimContext& ctx,
                                              Arena& arena) {
  if (!stmt->is_concurrent_clocked) return false;
  // §4.4.2.6 makes the action block's code reactive, so a blocking assignment
  // it makes and a #0 it executes belong to the reactive region set rather
  // than to the active one.
  auto* p =
      CreateAssertionChildProcess(ctx, arena, ConcurrentAssertActionRegion());
  p->is_reactive = true;
  p->coro = ConcurrentAssertActionCoroutine(action, ctx, arena).Release();
  ScheduleAssertionChildStart(p, p->home_region, ctx);
  return true;
}

// §16.5: "Concurrent assertions ... are evaluated in the Observed region", and
// §16.14.6 has one embedded in procedural code "evaluated as though it were a
// separate concurrent assertion", so where the statement is written does not
// change the region its property is evaluated in. A module-item concurrent
// assertion is carried by a process the scheduler already resumes there
// (Process::is_concurrent_clocked, see ResumeMaybeReactive in
// simulator/awaiters_event_control.h); one written inside a procedure is
// reached in whatever region that procedure is running in, which for an
// `always @(posedge clk)` is the Active region -- in the middle of the write
// that assigned the clock.
//
// The procedure suspends into the Observed region and resumes there rather than
// handing the property to a process of its own, because §16.14.6.1 evaluates
// the assertion against the scope the statement stands in: a variable of that
// procedure is reachable from this process and from no other. The statements
// after the assertion resume with it, which is the cost of the choice; §4.4.2.2
// keeps ordinary procedural code in the Active region, and a procedure with
// code after a concurrent assertion pays for the assertion's region.
struct ObservedRegionAwaiter {
  SimContext& ctx;

  bool await_ready() const noexcept {
    return ctx.GetScheduler().CurrentRegion() == Region::kObserved;
  }

  void await_suspend(std::coroutine_handle<> h) const {
    auto* proc = ctx.CurrentProcess();
    auto* event = ctx.GetScheduler().GetEventPool().Acquire();
    auto* ctx_ptr = &ctx;
    event->callback = [h, proc, ctx_ptr]() mutable {
      if (proc != nullptr && !proc->active) return;
      if (proc != nullptr) ctx_ptr->SetCurrentProcess(proc);
      h.resume();
    };
    ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), Region::kObserved,
                                     event);
  }

  void await_resume() const noexcept {}
};

// §16.3: records one evaluation of an immediate cover statement, succeeded
// when the covered expression held, against the statement in the scope the
// process stands in. No-op for assert/assume forms, and for the clocked
// boolean body a cover property is lowered to: that is a concurrent cover,
// whose results §16.14.3 defines over attempts and vacuity rather than these
// two counts, so it is not an immediate statement's result to report. A
// deferred cover's result is a pending report like its pass statement: §16.4.2
// has the point be flushed, and not reported as covered in that time step,
// when its process reaches a flush point before the report matures, so the
// evaluation is recorded only when the report runs in its region.
static void RecordCoverImmediateSample(const Stmt* stmt, bool is_true,
                                       SimContext& ctx) {
  if (stmt->kind != StmtKind::kCoverImmediate || stmt->is_concurrent_clocked) {
    return;
  }
  std::string scope = ScopeHierName(ctx);
  uint32_t line = stmt->range.start.line;
  if (!stmt->is_deferred) {
    ctx.ImmediateCovers().Record(scope, line, is_true);
    return;
  }
  SchedulePendingReport(stmt->is_final_deferred, stmt->label, ctx,
                        [scope, line, is_true, &ctx]() {
                          ctx.ImmediateCovers().Record(scope, line, is_true);
                        });
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

// §16.3 / §20.11: with no else clause the tool reports the violation via
// $error, unless $assertcontrol FailOff ($assertfailoff) has suppressed the
// fail action for this assertion's type and directive. The fail-action controls
// do not affect the statistics counters, so the failure is still counted even
// when its report is suppressed. §16.4.1: for a deferred assertion the default
// report is a pending report, scheduled with the process's other deferred
// reports rather than emitted here; a simple immediate assertion reports at
// once.
static void ReportDefaultAssertionFailure(const Stmt* stmt, uint32_t type_bit,
                                          uint32_t directive_bit,
                                          SimContext& ctx) {
  ctx.IncrementAssertionFailCount();
  if (!ctx.AssertFailActionEnabled(type_bit, directive_bit)) return;
  // §20.10: the tool-specific message carries the line of the statement, as
  // it carries a severity task's own line.
  uint32_t line = stmt->range.start.line;
  if (stmt->is_deferred) {
    ScheduleDeferredSeverityReport(stmt->is_final_deferred, stmt->label, line,
                                   ctx);
    return;
  }
  EmitSeverityHeader(ctx, "ERROR", "Assertion failed.", std::cerr, line);
}

// §16.5.1's mode raised around one evaluation of a concurrent assertion's
// property and lowered again before anything else runs, because the subclause
// reaches the assertion's own expression and nothing else in the source: the
// pass and fail statements are ordinary procedural code and read the values
// standing when they run. The previous setting is put back rather than cleared
// so that an immediate assertion reached from a function called by the property
// leaves the property's own reads sampled.
static bool EvalAssertionCondition(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  auto& samples = ctx.AssertionSamples();
  bool outer_evaluating_property = samples.EvaluatingProperty();
  samples.SetEvaluatingProperty(stmt->is_concurrent_clocked);
  auto cond = EvalExpr(stmt->assert_expr, ctx, arena);
  samples.SetEvaluatingProperty(outer_evaluating_property);
  return cond.IsTruthy();
}

// One attempt of the assertion from its evaluation on: the property is judged
// on §16.5.1's sampled values, the verdict's action block is scheduled where
// §16.4 or §4.4.2.6 puts it, and a failure with no action block is reported.
// Returns the action block the caller is to run where it stands, which is an
// immediate assertion's (§16.3), and nullptr where the action was scheduled
// elsewhere or there is none.
static const Stmt* JudgeAssertion(const Stmt* stmt, SimContext& ctx,
                                  Arena& arena) {
  // §16.3 / §20.11: the execution of immediate assertions can be controlled by
  // the assertion control system tasks. When $assertcontrol Off/Kill (or
  // $assertoff/$assertkill) has stopped checking for this assertion's type and
  // directive, the assertion is not evaluated, records nothing, and runs no
  // action on this activation.
  uint32_t type_bit = ImmediateAssertionTypeBit(stmt);
  uint32_t directive_bit = ImmediateDirectiveTypeBit(stmt);
  if (!ctx.AssertCheckingEnabled(type_bit, directive_bit)) return nullptr;

  bool is_true = EvalAssertionCondition(stmt, ctx, arena);
  RecordCoverImmediateSample(stmt, is_true, ctx);
  const Stmt* action =
      is_true ? stmt->assert_pass_stmt : stmt->assert_fail_stmt;
  if (action != nullptr) {
    if (TryScheduleDeferredAssertAction(action, stmt, ctx, arena) ||
        TryScheduleConcurrentAssertAction(action, stmt, ctx, arena)) {
      return nullptr;
    }
    return action;
  }
  if (!is_true && stmt->kind != StmtKind::kCoverImmediate) {
    ReportDefaultAssertionFailure(stmt, type_bit, directive_bit, ctx);
  }
  return nullptr;
}

// §16.9.4: the value each of the five future sampled value functions names is
// the argument's sampled value at the next global clocking tick, and the four
// predicates beside $future_gclk compare it with the value at the tick the
// function was called in. That second value is what this takes, one per call
// site under `root`, before the attempt waits for the global clocking tick that
// answers the first. The values are copied out of the variables they were read
// from, because the attempt keeps them across a tick the variables may change
// in.
using FutureGclkSamples = std::vector<std::pair<const Expr*, Logic4Vec>>;
static FutureGclkSamples* SampleFutureGclkOperands(const Expr* root,
                                                   SimContext& ctx,
                                                   Arena& arena) {
  auto* samples = arena.Create<FutureGclkSamples>();
  ForEachSubExpr(root, [&](const Expr* e) {
    GlobalClockingSampledFunction fn = GlobalClockingSampledFunction::kPastGclk;
    if (e->kind != ExprKind::kSystemCall) return;
    if (e->args.empty() || e->args[0] == nullptr) return;
    if (!ClassifyGlobalClockingSampledFunction(e->callee, fn)) return;
    if (!IsGlobalClockingFutureFunction(fn)) return;
    samples->emplace_back(e,
                          AssertionSampleStore::OwnedSample(
                              EvalSampledArg(e->args[0], ctx, arena), arena));
  });
  return samples;
}

// §16.9.4: one attempt of an assertion whose property names a future sampled
// value function, from its own tick to the global clocking tick that answers
// it. The attempt waits for that tick, evaluates the whole property there, and
// schedules its action block there, which is where the subclause has the
// action block of such an assertion run -- delayed to the global clocking tick
// that follows the last tick of the assertion clock for the attempt.
//
// What the attempt sampled at its own tick is written into the call sites'
// tick history just before the evaluation, so that EvalFutureGclk reads it
// back as the value one tick before the one it samples now. The history is
// written here rather than at the attempt's tick because an attempt the next
// tick starts would record over it before this one is answered: the sites are
// shared by every attempt of the assertion, and the tick history keeps one
// value per site.
//
// The whole property is evaluated at the later tick, so an operand of it that
// is not an argument of one of the five reads its sampled value there rather
// than at the assertion's tick. §16.9.4 puts the attempt's interval at the
// assertion clock, as though the future sampled values were known in advance,
// so a property mixing a future function with a plain operand reads the plain
// one a tick late. What that costs is one tick of a value the property also
// names directly, and what it buys is the five functions answering at all.
static SimCoroutine FutureGclkAttemptCoroutine(
    const Stmt* stmt, const std::vector<EventExpr>& gclk_event,
    const FutureGclkSamples* samples, SimContext& ctx, Arena& arena) {
  co_await EventAwaiter{ctx, gclk_event, arena};
  co_await ObservedRegionAwaiter{ctx};
  auto& store = ctx.AssertionSamples();
  for (const auto& [site, at_tick] : *samples) {
    store.RecordTick(site, at_tick, 1, arena);
  }
  // The statement carries a concurrent assertion's property, so the verdict's
  // action block is scheduled into the Reactive region rather than handed back
  // to be run here.
  JudgeAssertion(stmt, ctx, arena);
}

// §16.9.4: starts the attempt above in a process of its own, so that the
// process carrying the assertion is back at its clocking event for the next
// tick while this attempt waits for the global clocking tick that answers it.
// An attempt started at every tick of the assertion clock is what the
// subclause's interval asks for; an assertion that waited in its own process
// would start one attempt per two ticks, the wait consuming the tick between.
//
// The process is marked as carrying a concurrent assertion so that §16.5's
// rule resumes it in the Observed region of the global clocking tick, which is
// also where it starts: the asserting process is there already, and starting
// in the same region arms the wait before the tick can arrive.
static void StartFutureGclkAttempt(const Stmt* stmt, const Process& asserting,
                                   SimContext& ctx, Arena& arena) {
  auto* samples = SampleFutureGclkOperands(stmt->assert_expr, ctx, arena);
  auto* p = CreateAssertionChildProcess(ctx, arena, Region::kObserved);
  p->is_concurrent_clocked = true;
  p->coro = FutureGclkAttemptCoroutine(stmt, asserting.gclk_future_event,
                                       samples, ctx, arena)
                .Release();
  ScheduleAssertionChildStart(p, p->home_region, ctx);
}

ExecTask ExecImmediateAssert(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  // §16.5: a concurrent assertion's property is evaluated in the Observed
  // region, whether the statement stands outside procedural code or inside it.
  // An immediate assertion (§16.3) is not marked and is evaluated where it
  // stands.
  if (stmt->is_concurrent_clocked) co_await ObservedRegionAwaiter{ctx};

  // §16.9.4: an attempt of a property naming one of the five future sampled
  // value functions is answered at the global clocking tick that follows this
  // one, so it is handed to a process of its own and this process goes back to
  // its clocking event. Lowerer::LowerProcess carries the event onto the
  // process, and it is empty for every process whose property names none of
  // the five, which is every assertion in a design that uses none.
  Process* proc = ctx.CurrentProcess();
  if (proc != nullptr && !proc->gclk_future_event.empty()) {
    StartFutureGclkAttempt(stmt, *proc, ctx, arena);
    co_return StmtResult::kDone;
  }

  const Stmt* action = JudgeAssertion(stmt, ctx, arena);
  if (action != nullptr) co_return co_await ExecStmt(action, ctx, arena);
  co_return StmtResult::kDone;
}

// §16.4.5: a deferred immediate assertion may be written inside a function, and
// that function may be called by several different processes. Because a
// synchronous subroutine call does not change SimContext::CurrentProcess(), the
// assertion runs in the context of whichever process called the function, so
// its report is queued against that process's own pending-report generation
// (see §16.4.1/§16.4.2) and matures or is flushed independently of the other
// callers -- each process execution is independent.
//
// The function-body executor (ExecFuncStmt) is synchronous and cannot co_await.
// A deferred assertion never runs its action inline, only evaluating its
// expression and scheduling the pass/fail report into a later region, and a
// simple immediate assertion's action is an ordinary statement of the function
// body, so one attempt is judged here as ExecImmediateAssert judges it and the
// action a simple immediate assertion owes inline is returned for ExecFuncStmt
// to run, nullptr where there is none or it was scheduled elsewhere. §16.4.2's
// own example rests on the simple form: a function called to evaluate an
// action block's argument holds an assertion that reports on the call.
const Stmt* ExecImmediateAssertInFunction(const Stmt* stmt, SimContext& ctx,
                                          Arena& arena) {
  return JudgeAssertion(stmt, ctx, arena);
}

}  // namespace delta
