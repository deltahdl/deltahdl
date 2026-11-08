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

static bool DeferredReportCancelled(const Process& proc,
                                    std::string_view label) {
  return !label.empty() &&
         proc.cancelled_deferred_labels.count(std::string(label)) != 0;
}

static bool DeferredReportDropped(const Process* proc, uint64_t gen,
                                  const Stmt* stmt, uint64_t number) {
  if (proc == nullptr) return false;
  return proc->deferred_report_generation != gen ||
         number <= proc->queued_deferred_reports.at(stmt).flushed_through ||
         DeferredReportCancelled(*proc, stmt->label);
}

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

static void ScheduleDeferredSeverityReport(const Stmt* stmt, SourceLoc loc,
                                           SimContext& ctx) {
  SchedulePendingReport(stmt, ctx, [loc, &ctx]() {
    EmitSeverityHeader(ctx, "ERROR", "Assertion failed.", std::cerr, loc);
  });
}

static bool TryScheduleDeferredAssertAction(const Stmt* action,
                                            const Stmt* stmt, SimContext& ctx,
                                            Arena& arena) {
  if (!stmt->is_deferred) return false;
  ScheduleDeferredAction(action, stmt, ctx, arena);
  return true;
}

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
  p->rng_seed = ctx.DrawSeedForChild();
  return p;
}

void ScheduleAssertionChildStart(Process* p, Region region, SimContext& ctx) {
  auto* ev = ctx.GetScheduler().GetEventPool().Acquire();
  ev->callback = [p, &ctx]() {
    if (!p->active) return;
    ctx.SetCurrentProcess(p);
    p->Resume();
  };
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), region, ev);
}

static bool TryScheduleConcurrentAssertAction(const Stmt* action,
                                              const Stmt* stmt, SimContext& ctx,
                                              Arena& arena) {
  if (!stmt->is_concurrent_clocked) return false;
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

static void ReportDefaultAssertionFailure(const Stmt* stmt, SimContext& ctx) {
  ctx.IncrementAssertionFailCount();
  if (!AssertionControlStatus(stmt, ctx).fail_action) return;
  SourceLoc loc = stmt->range.start;
  if (stmt->is_deferred) {
    ScheduleDeferredSeverityReport(stmt, loc, ctx);
    return;
  }
  EmitSeverityHeader(ctx, "ERROR", "Assertion failed.", std::cerr, loc);
}

static bool EvalAssertionCondition(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  auto& samples = ctx.AssertionSamples();
  bool outer_evaluating_property = samples.EvaluatingProperty();
  samples.SetEvaluatingProperty(stmt->is_concurrent_clocked);
  auto cond = EvalExpr(stmt->assert_expr, ctx, arena);
  samples.SetEvaluatingProperty(outer_evaluating_property);
  return cond.IsTruthy();
}

static const Stmt* ConcludeAssertion(const Stmt* stmt, PropertyVerdict verdict,
                                     SimContext& ctx, Arena& arena) {
  bool is_true = verdict.holds;
  RecordCoverImmediateSample(stmt, is_true, ctx);
  NoteAttemptVerdict(stmt, verdict, ctx);
  const Stmt* action =
      is_true ? stmt->assert_pass_stmt : stmt->assert_fail_stmt;
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

static const Stmt* JudgeAssertion(const Stmt* stmt, SimContext& ctx,
                                  Arena& arena) {
  if (!AssertionControlStatus(stmt, ctx).checking) return nullptr;
  NoteAttemptBegun(stmt, ctx);
  const uint64_t kStarted =
      ctx.AssertionSamples().StepTime(ctx.CurrentTime()).ticks;

  if (stmt->assert_disable_iff != nullptr &&
      EvalExpr(stmt->assert_disable_iff, ctx, arena).IsTruthy()) {
    NoteAttemptDisabled(stmt, kStarted, ctx);
    return nullptr;
  }

  bool is_true = EvalAssertionCondition(stmt, ctx, arena);
  PropertyVerdict verdict;
  verdict.holds = is_true != stmt->assert_negated;
  verdict.started = kStarted;
  verdict.failed_at = stmt->assert_expr;
  return ConcludeAssertion(stmt, verdict, ctx, arena);
}

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

static AttemptInstances BegunAttempts(const Stmt* stmt,
                                      const AttemptInstances& instances,
                                      SimContext& ctx) {
  if (AssertionControlStatus(stmt, ctx).checking) return instances;
  return {};
}

static PropertyTreeState* PropertyTreeStateOf(const Stmt* stmt, Process& proc,
                                              SimContext& ctx, Arena& arena) {
  PropertyTreeState*& state = proc.property_tree_states[stmt];
  if (state == nullptr) {
    state = CreatePropertyTreeState(stmt->assert_property, stmt->assert_clock,
                                    stmt->cover_sequence, ctx, arena);
    if (state == nullptr) return nullptr;
    if (stmt->kind == StmtKind::kCoverImmediate ||
        stmt->kind == StmtKind::kExpect) {
      ReadPlainSequencesAsStrong(*state);
    }
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
    if (stmt->assert_strong != stmt->assert_negated) {
      RegisterStrongAttemptsFinal(stmt, state, ctx, arena);
    }
  }
  AttemptInstances begun = BegunAttempts(stmt, instances, ctx);
  for (size_t i = 0; i < begun.size(); ++i) NoteAttemptBegun(stmt, ctx);
  SequenceTick tick;
  tick.disabled = stmt->assert_disable_iff != nullptr &&
                  EvalExpr(stmt->assert_disable_iff, ctx, arena).IsTruthy();
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

struct FutureGclkAttempt {
  const Stmt* stmt;
  Process* owner;
  const AssertionSampleStore::Snapshot* own_tick;
  PendingReportScope scope;
};

static SimCoroutine FutureGclkAttemptCoroutine(
    FutureGclkAttempt attempt, const std::vector<EventExpr>& gclk_event,
    SimContext& ctx, Arena& arena) {
  co_await EventAwaiter{ctx, gclk_event, arena};
  co_await RegionAwaiter{ctx, Region::kObserved};
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

static void StartFutureGclkAttempt(const Stmt* stmt, Process& asserting,
                                   SimContext& ctx, Arena& arena) {
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
    auto& samples = ctx.AssertionSamples();
    for (const InstanceBindings* bindings : instances) {
      samples.SetInstanceBindings(bindings);
      JudgeAssertion(stmt, ctx, arena);
      samples.SetInstanceBindings(nullptr);
    }
  }
}

static void FlushKilledQueues(Process& proc,
                              const std::function<bool(const Stmt*)>& selects) {
  for (auto& [stmt, queued] : proc.queued_deferred_reports) {
    if (selects(stmt)) queued.flushed_through = queued.latest;
  }
  for (auto& [stmt, state] : proc.procedural_assertions) {
    if (selects(stmt)) state->pending.clear();
  }
}

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
  if (stmt->is_procedural_concurrent && stmt->is_concurrent_clocked &&
      !stmt->assert_clock.empty() &&
      EnqueueProceduralAssertion(stmt, ctx, arena)) {
    co_return StmtResult::kDone;
  }
  if (stmt->is_concurrent_clocked)
    co_await RegionAwaiter{ctx, Region::kObserved};

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

const Stmt* ExecImmediateAssertInFunction(const Stmt* stmt, SimContext& ctx,
                                          Arena& arena) {
  return JudgeAssertion(stmt, ctx, arena);
}

}  // namespace delta
