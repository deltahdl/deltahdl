#include <cstddef>
#include <cstdint>
#include <cstring>
#include <functional>
#include <iostream>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/assert_control_log.h"
#include "simulator/assertion_attempt_events.h"
#include "simulator/awaiters_event_control.h"
#include "simulator/cover_results.h"
#include "simulator/evaluation.h"
#include "simulator/exec_task.h"
#include "simulator/instance_bindings.h"
#include "simulator/instance_prefix_override.h"
#include "simulator/procedural_assertion.h"
#include "simulator/process.h"
#include "simulator/property_attempts.h"
#include "simulator/scheduler.h"
#include "simulator/scope_hier_name.h"
#include "simulator/sequence_monitor.h"
#include "simulator/sim_context.h"
#include "simulator/statement_coverage.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_exec_assertion_internal.h"
#include "simulator/stmt_exec_internal.h"
#include "simulator/stmt_result.h"
#include "simulator/sva_engine_queues.h"
#include "simulator/sva_engine_sampling.h"

namespace delta {

static void RunDeferredActionSync(const Stmt* action, SimContext& ctx,
                                  Arena& arena) {
  if (!action) return;
  // §40.2.2: the action runs here rather than through ExecStmt, and counts as
  // executed for statement coverage all the same.
  NoteStatementExecuted(action, ctx);
  switch (action->kind) {
    case StmtKind::kNull:
      return;
    case StmtKind::kExprStmt:

      if (!TryExecSystemCallTask(action->expr, ctx, arena)) {
        EvalExpr(action->expr, ctx, arena);
      }
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
// cancelled by a `disable <assertion_label>` statement in `proc` (see
// Process::cancelled_deferred_labels). An unlabeled assertion cannot be named
// by a disable, so an empty label is never cancelled.
static bool DeferredReportCancelled(const Process& proc,
                                    std::string_view label) {
  return !label.empty() &&
         proc.cancelled_deferred_labels.count(std::string(label)) != 0;
}

// §16.4 with §20.11 and §39.5.3: whether the report `proc` queued for `stmt`
// under the generation `gen`, numbered `number`, is no longer to run: flushed
// by a flush point of the process, which bumped the generation, or by a Kill
// selecting the assertion since the report was queued, or cancelled.
static bool DeferredReportDropped(const Process* proc, uint64_t gen,
                                  const Stmt* stmt, uint64_t number) {
  if (proc == nullptr) return false;
  return proc->deferred_report_generation != gen ||
         number <= proc->queued_deferred_reports.at(stmt).flushed_through ||
         DeferredReportCancelled(*proc, stmt->label);
}

// §16.4.1 and §16.4.2: queues one pending report of the deferred assertion
// `stmt` -- an action block's subroutine call, the default $error, or a
// deferred cover's result -- in the Reactive region for an observed deferred
// assertion and the Postponed region for a final one, where `run` executes
// it. The process and its report generation are captured now; if a flush
// point bumps the generation before the region fires (the process resumes, or
// an always_comb re-triggers in the same time step), or a Kill selects the
// assertion (§20.11, §39.5.3), the queued report has been flushed and is
// skipped, as it is when §16.4.4's `disable <assertion_label>` has cancelled
// it.
static void SchedulePendingReport(const Stmt* stmt, SimContext& ctx,
                                  std::function<void()> run) {
  Region region =
      stmt->is_final_deferred ? Region::kPostponed : Region::kReactive;
  PendingReportScope scope = PendingReportScope::Capture(ctx);
  uint64_t gen = ctx.CurrentDeferredReportGeneration();
  uint64_t number = 0;
  if (scope.proc != nullptr) {
    number = ++scope.proc->deferred_reports_queued;
    scope.proc->queued_deferred_reports[stmt].latest = number;
  }
  auto* ev = ctx.GetScheduler().GetEventPool().Acquire();
  ev->callback = [scope, gen, stmt, number, run = std::move(run), &ctx]() {
    if (DeferredReportDropped(scope.proc, gen, stmt, number)) return;
    PendingReportScope saved;
    scope.Install(ctx, saved);
    run();
    PendingReportScope::Restore(ctx, saved);
  };
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), region, ev);
}

static void ScheduleDeferredAction(const Stmt* action, const Stmt* stmt,
                                   SimContext& ctx, Arena& arena) {
  if (!action) return;
  DeferredArgSnapshots snaps = SnapshotDeferredCallArgs(action, ctx, arena);
  SchedulePendingReport(
      stmt, ctx, [action, snaps = std::move(snaps), &ctx, &arena]() {
        RunDeferredActionWithSnapshots(action, snaps, ctx, arena);
      });
}

// §16.4.1: when a deferred assertion fails with no else clause, its default
// $error report is a pending assertion report rather than an immediate one.
// Like the action-block subroutine call, it is not emitted where the assertion
// is processed; it is deferred and executed with the rest of the process's
// pending reports.
static void ScheduleDeferredSeverityReport(const Stmt* stmt, SourceLoc loc,
                                           SimContext& ctx) {
  SchedulePendingReport(stmt, ctx, [loc, &ctx]() {
    EmitSeverityHeader(ctx, "ERROR", "Assertion failed.", std::cerr, loc);
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
  ScheduleDeferredAction(action, stmt, ctx, arena);
  return true;
}

// §4.4.2.6: the Reactive region is where blocking assignments in checkers and
// program blocks are scheduled, and the action blocks of concurrent assertions
// with them, which §4.4.2.5 states again from the property's side: pass and
// fail code that property evaluation produces is scheduled in the current time
// slot's Reactive region. The action therefore does not run
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
// §21.2.1.5 has %m name the scope the statement stands in, which for an
// action block is the assertion's label, as §16.5.2's own example prints
// "%m, passing" to say which assertion passed. The child process starts from
// an event of its region with the context's named scopes whatever ran last, so
// the scopes standing when the attempt scheduled the action are stood up
// around it and put back after.
//
// §16.14.6.1: the action block of a procedural concurrent assertion reads the
// values its instance saved as the property does, so the bindings standing
// when the attempt scheduled the action are stood up around it as well.
static SimCoroutine ConcurrentAssertActionCoroutine(
    const Stmt* action, std::vector<std::string_view> named_scopes,
    const InstanceBindings* bindings, SimContext& ctx, Arena& arena) {
  PendingReportScope scope;
  scope.proc = ctx.CurrentProcess();
  scope.named_scopes = std::move(named_scopes);
  PendingReportScope saved;
  scope.Install(ctx, saved);
  ctx.AssertionSamples().SetInstanceBindings(bindings);
  co_await ExecStmt(action, ctx, arena);
  ctx.AssertionSamples().SetInstanceBindings(nullptr);
  PendingReportScope::Restore(ctx, saved);
}

// A process a concurrent assertion hands part of an attempt to: its action
// block (§4.4.2.6), or the attempt itself where §16.9.4 answers it at a later
// tick. §23.6 resolves the names it writes under the instance and generate
// prefixes the assertion stands in, so the process carries the ones the
// process that reached the assertion had.
Process* CreateAssertionChildProcess(SimContext& ctx, Arena& arena,
                                     Region home_region) {
  auto* p = arena.Create<Process>();
  p->kind = ProcessKind::kInitial;
  p->home_region = home_region;
  if (auto* asserting = ctx.CurrentProcess()) {
    p->inst_prefix = asserting->inst_prefix;
    p->gen_prefixes = asserting->gen_prefixes;
    p->gen_block_name = asserting->gen_block_name;
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
void ScheduleAssertionChildStart(Process* p, Region region, SimContext& ctx) {
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
  p->coro = ConcurrentAssertActionCoroutine(action, ctx.ActiveNamedScopes(),
                                            ctx.AssertionSamples().Bindings(),
                                            ctx, arena)
                .Release();
  ScheduleAssertionChildStart(p, p->home_region, ctx);
  return true;
}

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
  SchedulePendingReport(stmt, ctx, [scope, line, is_true, &ctx]() {
    ctx.ImmediateCovers().Record(scope, line, is_true);
  });
}

// §20.11: the Table 20-6 assertion_type bit that identifies an assertion
// statement -- an expect statement, a concurrent assertion, or a simple
// immediate, observed deferred or final deferred one -- so a $assertcontrol
// assertion_type mask can select whether it is controlled.
static uint32_t AssertionTypeBitOf(const Stmt* stmt) {
  if (stmt->kind == StmtKind::kExpect) {
    return static_cast<uint32_t>(AssertionTypeBit::kExpect);
  }
  if (stmt->is_concurrent_clocked) {
    return static_cast<uint32_t>(AssertionTypeBit::kConcurrent);
  }
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
static uint32_t DirectiveTypeBitOf(const Stmt* stmt) {
  switch (stmt->kind) {
    case StmtKind::kCoverImmediate:
      return static_cast<uint32_t>(DirectiveTypeBit::kCover);
    case StmtKind::kAssumeImmediate:
      return static_cast<uint32_t>(DirectiveTypeBit::kAssume);
    default:
      return static_cast<uint32_t>(DirectiveTypeBit::kAssert);
  }
}

// §20.11: the assertion `stmt` as a control selects it, written in the scope
// named `scope`, its own name kept in `name`: its full name where it is
// labelled, and where it is not, the key §39.3.1 has a VPI control name it
// by, which no task's scope list can write. An empty scope leaves both names
// out, for a run whose controls name no scope list.
static AssertionIdentity IdentityOf(const Stmt* stmt, std::string_view scope,
                                    std::string& name, SimContext& ctx) {
  if (!scope.empty()) name = RunAssertionKey(stmt, scope, ctx);
  return {AssertionTypeBitOf(stmt), DirectiveTypeBitOf(stmt), scope, name};
}

AssertionStatus AssertionControlStatus(const Stmt* stmt, SimContext& ctx) {
  AssertControlLog& controls = ctx.AssertControls();
  std::string scope;
  if (controls.NamesScopes()) scope = ScopeHierName(ctx);
  std::string name;
  return controls.StatusOf(IdentityOf(stmt, scope, name, ctx));
}

// §16.3 / §20.11: with no else clause the tool reports the violation via
// $error, unless $assertcontrol FailOff ($assertfailoff) has suppressed the
// fail action for this assertion. The fail-action controls
// do not affect the statistics counters, so the failure is still counted even
// when its report is suppressed. §16.4.1: for a deferred assertion the default
// report is a pending report, scheduled with the process's other deferred
// reports rather than emitted here; a simple immediate assertion reports at
// once.
static void ReportDefaultAssertionFailure(const Stmt* stmt, SimContext& ctx) {
  ctx.IncrementAssertionFailCount();
  if (!AssertionControlStatus(stmt, ctx).fail_action) return;
  // §20.10: the tool-specific message carries the file and line of the
  // statement, as it carries a severity task's own.
  SourceLoc loc = stmt->range.start;
  if (stmt->is_deferred) {
    ScheduleDeferredSeverityReport(stmt, loc, ctx);
    return;
  }
  EmitSeverityHeader(ctx, "ERROR", "Assertion failed.", std::cerr, loc);
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

// The assertion's verdict at one attempt: a cover's sample is recorded, the
// verdict's action block is scheduled where §16.4 or §4.4.2.6 puts it, and a
// failure with no action block is reported. Returns the action block the
// caller is to run where it stands, which is an immediate assertion's
// (§16.3), and nullptr where the action was scheduled elsewhere or there is
// none.
static const Stmt* ConcludeAssertion(const Stmt* stmt, PropertyVerdict verdict,
                                     SimContext& ctx, Arena& arena) {
  bool is_true = verdict.holds;
  RecordCoverImmediateSample(stmt, is_true, ctx);
  NoteAttemptVerdict(stmt, verdict, ctx);
  const Stmt* action =
      is_true ? stmt->assert_pass_stmt : stmt->assert_fail_stmt;
  // §16.17: an expect statement's verdict unblocks the process it stands
  // in, which runs the action block itself once it resumes; a failure with
  // no else clause is reported through $error here.
  if (stmt->kind == StmtKind::kExpect) {
    if (Process* proc = ctx.CurrentProcess()) {
      proc->expect_decided = true;
      proc->expect_holds = is_true;
    }
    if (!is_true && action == nullptr) {
      ReportDefaultAssertionFailure(stmt, ctx);
    }
    return nullptr;
  }
  if (action != nullptr) {
    // §20.11: PassOff, VacuousOff and FailOff stop the action block of the
    // verdict they apply to.
    if (!AssertionControlStatus(stmt, ctx).RunsAction(is_true,
                                                      verdict.vacuous)) {
      return nullptr;
    }
    if (TryScheduleDeferredAssertAction(action, stmt, ctx, arena) ||
        TryScheduleConcurrentAssertAction(action, stmt, ctx, arena)) {
      return nullptr;
    }
    return action;
  }
  if (!is_true && stmt->kind != StmtKind::kCoverImmediate) {
    ReportDefaultAssertionFailure(stmt, ctx);
  }
  return nullptr;
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
  if (!AssertionControlStatus(stmt, ctx).checking) return nullptr;
  NoteAttemptBegun(stmt, ctx);
  const uint64_t kStarted =
      ctx.AssertionSamples().StepTime(ctx.CurrentTime()).ticks;

  // §16.12: an attempt at which the disable condition, read as the variables
  // stand rather than sampled, is true is disabled: it neither succeeds nor
  // fails, so no action block runs and no failure is reported.
  if (stmt->assert_disable_iff != nullptr &&
      EvalExpr(stmt->assert_disable_iff, ctx, arena).IsTruthy()) {
    NoteAttemptDisabled(stmt, kStarted, ctx);
    return nullptr;
  }

  // §16.12.3: `not` returns the opposite of the underlying evaluation.
  bool is_true = EvalAssertionCondition(stmt, ctx, arena);
  PropertyVerdict verdict;
  verdict.holds = is_true != stmt->assert_negated;
  verdict.started = kStarted;
  verdict.failed_at = stmt->assert_expr;
  return ConcludeAssertion(stmt, verdict, ctx, arena);
}

// §16.12.2: one tick of a sequential property. The attempts in flight and
// the one this tick begins advance over §16.5.1's sampled values, and each
// that reaches its verdict at this tick, matching or failing, concludes the
// assertion as a boolean property's evaluation does; the attempts still in
// flight when the run ends fail then where the property is strong, or, as
// §16.12.3 has `not` switch the strength, weak and negated.
//
// The final process runs with the context holding whatever ran last, so the
// scopes the assertion stands in, its label among them, are captured where
// the process is registered, at the statement's first tick, and stood up
// around the reports, which §21.2.1.5 and §16.14.3's results name by them.
static SimCoroutine StrongAttemptsFinalCoroutine(const Stmt* stmt,
                                                 SequencePropertyState* state,
                                                 PendingReportScope scope,
                                                 SimContext& ctx,
                                                 Arena& arena) {
  PendingReportScope saved;
  scope.Install(ctx, saved);
  for (uint64_t started : PendingSequenceStarts(*state)) {
    RecordCoverImmediateSample(stmt, false, ctx);
    PropertyVerdict failed;
    failed.started = started;
    NoteAttemptVerdict(stmt, failed, ctx);
    if (stmt->assert_fail_stmt == nullptr) {
      if (stmt->kind != StmtKind::kCoverImmediate) {
        ReportDefaultAssertionFailure(stmt, ctx);
      }
    } else if (AssertionControlStatus(stmt, ctx).fail_action) {
      co_await ExecStmt(stmt->assert_fail_stmt, ctx, arena);
    }
  }
  PendingReportScope::Restore(ctx, saved);
}

static void RegisterStrongAttemptsFinal(const Stmt* stmt,
                                        SequencePropertyState* state,
                                        SimContext& ctx, Arena& arena) {
  auto* p = CreateAssertionChildProcess(ctx, arena, Region::kActive);
  p->kind = ProcessKind::kFinal;
  p->coro = StrongAttemptsFinalCoroutine(
                stmt, state, PendingReportScope::Capture(ctx), ctx, arena)
                .Release();
  ctx.RegisterFinalProcess(p);
}

// §16.12.4 and §16.12.5: one tick of a property of operands under or and
// and, evaluated as the sequential property above is, each attempt's tree
// deciding the assertion's verdict, and the attempts still in flight when
// the run ends decided then in a final process with their sequences read by
// their strength.
static SimCoroutine PropertyTreeFinalCoroutine(const Stmt* stmt,
                                               PropertyTreeState* state,
                                               PendingReportScope scope,
                                               SimContext& ctx, Arena& arena) {
  PendingReportScope saved;
  scope.Install(ctx, saved);
  for (PropertyVerdict verdict : FinishPropertyTree(*state)) {
    RecordCoverImmediateSample(stmt, verdict.holds, ctx);
    NoteAttemptVerdict(stmt, verdict, ctx);
    const Stmt* action =
        verdict.holds ? stmt->assert_pass_stmt : stmt->assert_fail_stmt;
    if (action == nullptr) {
      if (!verdict.holds && stmt->kind != StmtKind::kCoverImmediate) {
        ReportDefaultAssertionFailure(stmt, ctx);
      }
    } else if (AssertionControlStatus(stmt, ctx).RunsAction(verdict.holds,
                                                            verdict.vacuous)) {
      ctx.AssertionSamples().SetInstanceBindings(verdict.bindings);
      co_await ExecStmt(action, ctx, arena);
      ctx.AssertionSamples().SetInstanceBindings(nullptr);
    }
  }
  PendingReportScope::Restore(ctx, saved);
}

// §20.11: the attempts `instances` begin at this tick, none where Off or Kill
// has stopped the assertion's checking. Off leaves an attempt already under
// way to run on to its verdict, and Kill has aborted every one.
static AttemptInstances BegunAttempts(const Stmt* stmt,
                                      const AttemptInstances& instances,
                                      SimContext& ctx) {
  if (AssertionControlStatus(stmt, ctx).checking) return instances;
  return {};
}

// The attempts of the property tree `stmt` carries that `proc` keeps, made
// at the first tick it is reached at, where the watchers on its clocks are
// installed and its final evaluation is registered; nullptr where the tree
// cannot be read.
static PropertyTreeState* PropertyTreeStateOf(const Stmt* stmt, Process& proc,
                                              SimContext& ctx, Arena& arena) {
  PropertyTreeState*& state = proc.property_tree_states[stmt];
  if (state == nullptr) {
    state = CreatePropertyTreeState(stmt->assert_property, stmt->assert_clock,
                                    stmt->cover_sequence, ctx, arena);
    if (state == nullptr) return nullptr;
    auto* p = CreateAssertionChildProcess(ctx, arena, Region::kActive);
    p->kind = ProcessKind::kFinal;
    p->coro = PropertyTreeFinalCoroutine(
                  stmt, state, PendingReportScope::Capture(ctx), ctx, arena)
                  .Release();
    ctx.RegisterFinalProcess(p);
  }
  return state;
}

static void ExecPropertyTreeTick(const Stmt* stmt,
                                 const AttemptInstances& instances,
                                 SimContext& ctx, Arena& arena,
                                 Process* owner) {
  Process* proc = owner != nullptr ? owner : ctx.CurrentProcess();
  PropertyTreeState* state =
      proc == nullptr ? nullptr : PropertyTreeStateOf(stmt, *proc, ctx, arena);
  if (state == nullptr) return;
  bool disabled = stmt->assert_disable_iff != nullptr &&
                  EvalExpr(stmt->assert_disable_iff, ctx, arena).IsTruthy();
  auto& samples = ctx.AssertionSamples();
  bool outer_evaluating_property = samples.EvaluatingProperty();
  samples.SetEvaluatingProperty(true);
  AttemptReads reads(stmt, ctx);
  PropertyTick tick = AdvancePropertyTree(
      *state, disabled, BegunAttempts(stmt, instances, ctx), ctx, arena);
  samples.SetEvaluatingProperty(outer_evaluating_property);
  for (uint32_t i = 0; i < tick.attempted; ++i) NoteAttemptBegun(stmt, ctx);
  for (uint64_t started : tick.disabled) {
    NoteAttemptDisabled(stmt, started, ctx);
  }
  reads.Finish(tick.verdicts);
  for (PropertyVerdict verdict : tick.verdicts) {
    // §16.14.6.1: the action block scheduled for the verdict reads what the
    // instance saved, so the bindings stand while it is scheduled.
    samples.SetInstanceBindings(verdict.bindings);
    ConcludeAssertion(stmt, verdict, ctx, arena);
    samples.SetInstanceBindings(nullptr);
  }
}

static void ExecSequencePropertyTick(const Stmt* stmt,
                                     const AttemptInstances& instances,
                                     SimContext& ctx, Arena& arena,
                                     Process* owner) {
  Process* proc = owner != nullptr ? owner : ctx.CurrentProcess();
  if (proc == nullptr) return;
  SequencePropertyState*& state = proc->sequence_property_states[stmt];
  if (state == nullptr) {
    state = CreateSequencePropertyState(stmt->assert_sequence, ctx, arena);
    if (state == nullptr) return;
    // §16.12.3: `not` switches the strength, so the attempts unfinished at
    // the end fail under strong, and under weak once negated.
    if (stmt->assert_strong != stmt->assert_negated) {
      RegisterStrongAttemptsFinal(stmt, state, ctx, arena);
    }
  }
  AttemptInstances begun = BegunAttempts(stmt, instances, ctx);
  for (size_t i = 0; i < begun.size(); ++i) NoteAttemptBegun(stmt, ctx);
  SequenceTick tick;
  tick.disabled = stmt->assert_disable_iff != nullptr &&
                  EvalExpr(stmt->assert_disable_iff, ctx, arena).IsTruthy();
  // §16.14.3: a cover sequence's attempt stays in flight past a match, every
  // match of it counted; a property, a cover property's among them, holds
  // at the first.
  tick.every_match = stmt->cover_sequence;
  tick.instances = begun;
  auto& samples = ctx.AssertionSamples();
  bool outer_evaluating_property = samples.EvaluatingProperty();
  samples.SetEvaluatingProperty(true);
  AttemptReads reads(stmt, ctx);
  std::vector<SequenceOutcome> outcomes =
      AdvanceSequenceProperty(*state, tick, ctx, arena);
  samples.SetEvaluatingProperty(outer_evaluating_property);
  std::vector<PropertyVerdict> decided;
  for (const SequenceOutcome& outcome : outcomes) {
    if (outcome.verdict == SequenceVerdict::kDisabled) {
      NoteAttemptDisabled(stmt, outcome.started, ctx);
      continue;
    }
    bool matched = outcome.verdict == SequenceVerdict::kMatched;
    PropertyVerdict& verdict = decided.emplace_back();
    verdict.holds = matched != stmt->assert_negated;
    verdict.bindings = outcome.bindings;
    verdict.started = outcome.started;
  }
  reads.Finish(decided);
  for (const PropertyVerdict& verdict : decided) {
    samples.SetInstanceBindings(verdict.bindings);
    ConcludeAssertion(stmt, verdict, ctx, arena);
    samples.SetInstanceBindings(nullptr);
  }
}

// §16.9.4: one step of an assertion whose property names a future sampled
// value function, from its tick of the assertion clock to the global clocking
// tick that answers it: the statement, the process that keeps its attempts in
// flight, what was sampled at its tick, and the process and named scopes the
// assertion stands in, its label among them, captured where the step starts so
// that the verdict's report names the assertion as §20.10 has it.
struct FutureGclkAttempt {
  const Stmt* stmt;
  Process* owner;
  const AssertionSampleStore::Snapshot* own_tick;
  PendingReportScope scope;
};

// The step waits for that tick and is taken there, which is where the clause
// has the action block of such an assertion run -- delayed to the global
// clocking tick that follows the last tick of the assertion clock for the
// attempt. The clause puts the attempt's interval at the assertion clock, as
// though the future values were known in advance, so the step reads what was
// sampled at its own tick and stands in that time step; a future function
// alone reads its argument past the snapshot, for the value at this tick. A
// boolean property is one attempt decided here; a property of operators and a
// sequence advance each attempt the owner keeps by the one tick, so their
// steps are taken one after another, in the order of their ticks.
static SimCoroutine FutureGclkAttemptCoroutine(
    FutureGclkAttempt attempt, const std::vector<EventExpr>& gclk_event,
    SimContext& ctx, Arena& arena) {
  co_await EventAwaiter{ctx, gclk_event, arena};
  co_await RegionAwaiter{ctx, Region::kObserved};
  // The statement carries a concurrent assertion's property, so the verdict's
  // action block is scheduled into the Reactive region rather than handed back
  // to be run here.
  attempt.scope.proc = ctx.CurrentProcess();
  PendingReportScope saved;
  attempt.scope.Install(ctx, saved);
  const Stmt* stmt = attempt.stmt;
  AttemptInstances one{nullptr};
  ctx.AssertionSamples().SetSnapshot(attempt.own_tick);
  if (stmt->assert_property != nullptr) {
    ExecPropertyTreeTick(stmt, one, ctx, arena, attempt.owner);
  } else if (stmt->assert_sequence != nullptr) {
    ExecSequencePropertyTick(stmt, one, ctx, arena, attempt.owner);
  } else {
    JudgeAssertion(stmt, ctx, arena);
  }
  ctx.AssertionSamples().SetSnapshot(nullptr);
  PendingReportScope::Restore(ctx, saved);
}

// §16.9.4: starts the step above in a process of its own, so that the process
// carrying the assertion is back at its clocking event for the next tick while
// this one waits for the global clocking tick that answers it. A step started
// at every tick of the assertion clock is what the subclause's interval asks
// for; an assertion that waited in its own process would take one step per two
// ticks, the wait consuming the tick between.
//
// The process is marked as carrying a concurrent assertion so that §16.5's
// rule resumes it in the Observed region of the global clocking tick, which is
// also where it starts: the asserting process is there already, and starting
// in the same region arms the wait before the tick can arrive. A boolean
// property's step is its one attempt, which a Kill aborts with the process; a
// step of the other two advances every attempt in flight, which a Kill aborts
// where the owner keeps them.
static void StartFutureGclkAttempt(const Stmt* stmt, Process& asserting,
                                   SimContext& ctx, Arena& arena) {
  // A tree's attempts are made here, at the tick, so that the watchers on its
  // clocks record every tick from it on for the steps that read them later.
  if (stmt->assert_property != nullptr) {
    PropertyTreeStateOf(stmt, asserting, ctx, arena);
  }
  const auto* own_tick =
      ctx.AssertionSamples().TakeSnapshot(ctx.CurrentTime(), arena);
  auto* p = CreateAssertionChildProcess(ctx, arena, Region::kObserved);
  p->is_concurrent_clocked = true;
  if (stmt->assert_property == nullptr && stmt->assert_sequence == nullptr) {
    p->future_gclk_attempt_of = stmt;
  }
  FutureGclkAttempt attempt{stmt, &asserting, own_tick,
                            PendingReportScope::Capture(ctx)};
  p->coro = FutureGclkAttemptCoroutine(std::move(attempt),
                                       asserting.gclk_future_event, ctx, arena)
                .Release();
  ScheduleAssertionChildStart(p, p->home_region, ctx);
}

void ExecConcurrentAssertionTick(const Stmt* stmt,
                                 const AttemptInstances& instances,
                                 SimContext& ctx, Arena& arena) {
  if (stmt->assert_property != nullptr) {
    ExecPropertyTreeTick(stmt, instances, ctx, arena, nullptr);
  } else if (stmt->assert_sequence != nullptr) {
    ExecSequencePropertyTick(stmt, instances, ctx, arena, nullptr);
  } else {
    // A boolean property is decided at its own tick, so each attempt is one
    // evaluation, reading what its instance saved (§16.14.6.1); its action
    // block, a concurrent assertion's, is scheduled into the Reactive
    // region rather than handed back.
    auto& samples = ctx.AssertionSamples();
    for (const InstanceBindings* bindings : instances) {
      samples.SetInstanceBindings(bindings);
      JudgeAssertion(stmt, ctx, arena);
      samples.SetInstanceBindings(nullptr);
    }
  }
}

// §20.11 and §39.5.3: a Kill also flushes the pending reports `proc` queued
// for the deferred assertions it `selects` and the pending instances of the
// procedural concurrent ones, neither of which has matured.
static void FlushKilledQueues(Process& proc,
                              const std::function<bool(const Stmt*)>& selects) {
  for (auto& [stmt, queued] : proc.queued_deferred_reports) {
    if (selects(stmt)) queued.flushed_through = queued.latest;
  }
  for (auto& [stmt, state] : proc.procedural_assertions) {
    if (selects(stmt)) state->pending.clear();
  }
}

// The attempts in flight that `proc` keeps of the assertions the Kill `call`
// selects and no Lock holds, aborted. §16.9.4: an attempt waiting in a
// process of its own for the global clocking tick is aborted with the
// process.
static void AbortProcessAttempts(Process& proc, const AssertControlCall& call,
                                 SimContext& ctx) {
  std::string scope;
  if (!call.scopes.empty()) scope = ProcessHierName(proc, ctx);
  auto selects = [&](const Stmt* stmt) {
    std::string name;
    AssertionIdentity identity = IdentityOf(stmt, scope, name, ctx);
    return CallSelects(call, identity) &&
           !ctx.AssertControls().StatusOf(identity).locked;
  };
  if (proc.future_gclk_attempt_of != nullptr &&
      selects(proc.future_gclk_attempt_of)) {
    proc.active = false;
    NoteAttemptsKilled(proc.future_gclk_attempt_of, proc, 1, ctx);
  }
  for (auto& [stmt, state] : proc.property_tree_states) {
    if (state != nullptr && selects(stmt)) {
      NoteAttemptsKilled(stmt, proc, AbortPropertyTreeAttempts(*state), ctx);
    }
  }
  for (auto& [stmt, state] : proc.sequence_property_states) {
    if (state != nullptr && selects(stmt)) {
      NoteAttemptsKilled(stmt, proc, AbortSequencePropertyAttempts(*state),
                         ctx);
    }
  }
  FlushKilledQueues(proc, selects);
  // §20.11: a Kill also flushes the queued violation reports of the types it
  // selects (§12.4.2.1, §12.5.3.1) that have not yet matured.
  std::erase_if(proc.pending_violations,
                [&](const Process::PendingViolation& v) {
                  AssertionIdentity identity{v.type_bit, 0, v.scope, {}};
                  return CallSelects(call, identity) &&
                         !ctx.AssertControls().StatusOf(identity).locked;
                });
}

void AbortKilledAttempts(const AssertControlCall& call, SimContext& ctx) {
  for (Process* proc : ctx.GetScheduler().Threads()) {
    AbortProcessAttempts(*proc, call, ctx);
  }
}

ExecTask ExecImmediateAssert(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  // §16.14.6: a concurrent assertion embedded in procedural code is not
  // evaluated where it is reached but placed in the procedural assertion
  // queue of the process, to be evaluated at its leading clocking event.
  if (stmt->is_procedural_concurrent && stmt->is_concurrent_clocked &&
      !stmt->assert_clock.empty() &&
      EnqueueProceduralAssertion(stmt, ctx, arena)) {
    co_return StmtResult::kDone;
  }
  // §16.5: a concurrent assertion's property is evaluated in the Observed
  // region, whether the statement stands outside procedural code or inside it.
  // An immediate assertion (§16.3) is not marked and is evaluated where it
  // stands.
  if (stmt->is_concurrent_clocked)
    co_await RegionAwaiter{ctx, Region::kObserved};

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

  if (stmt->assert_property != nullptr) {
    ExecPropertyTreeTick(stmt, AttemptInstances{nullptr}, ctx, arena, nullptr);
    co_return StmtResult::kDone;
  }
  if (stmt->assert_sequence != nullptr) {
    ExecSequencePropertyTick(stmt, AttemptInstances{nullptr}, ctx, arena,
                             nullptr);
    co_return StmtResult::kDone;
  }

  const Stmt* action = JudgeAssertion(stmt, ctx, arena);
  if (action != nullptr) co_return co_await ExecStmt(action, ctx, arena);
  co_return StmtResult::kDone;
}

// §17.3: reaching the instantiation places a pending instance of each static
// concurrent assertion of the procedural checker instance in the procedural
// assertion queue of the process, and adds each static deferred assertion to
// the process's pending deferred assertion reports, as a procedural one
// standing at the instantiation would be; the deferred one is evaluated, and
// its report later run, in the checker's instance.
ExecTask ExecCheckerInstantiation(const Stmt* stmt, SimContext& ctx,
                                  Arena& arena) {
  const auto& assertions =
      ctx.CurrentProcess()->checker_instance_assertions[stmt];
  for (const ProceduralCheckerAssertion* assertion : assertions) {
    if (assertion->state != nullptr) {
      EnqueueProceduralCheckerAssertion(*assertion, ctx, arena);
      continue;
    }
    InstancePrefixOverride in_checker(ctx.InstancePrefixOverride(),
                                      assertion->inst_prefix);
    co_await ExecImmediateAssert(assertion->stmt, ctx, arena);
  }
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
