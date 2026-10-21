#include "simulator/assertion_attempt_events.h"

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "parser/ast_stmt.h"
#include "simulator/assertion_api.h"
#include "simulator/assertion_coverage.h"
#include "simulator/awaiters_event_control.h"
#include "simulator/code_coverage.h"
#include "simulator/cover_results.h"
#include "simulator/cover_statement.h"
#include "simulator/process.h"
#include "simulator/property_attempts.h"
#include "simulator/scheduler.h"
#include "simulator/scope_hier_name.h"
#include "simulator/sequence_monitor.h"
#include "simulator/sim_context.h"
#include "simulator/stmt_exec_assertion_internal.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/sva_engine_sampling.h"
#include "simulator/vpi_expr_decompile.h"

namespace delta {

namespace {

// §16.14.3: the results record of a concurrent cover statement, the clocked
// body a cover property or a cover sequence is lowered to, in the scope the
// process stands in; nullptr for every other assertion statement.
ConcurrentCoverResult* ConcurrentCoverRecord(const Stmt* stmt,
                                             SimContext& ctx) {
  if (stmt->kind != StmtKind::kCoverImmediate || !stmt->is_concurrent_clocked) {
    return nullptr;
  }
  return &ctx.ConcurrentCovers().Record(
      ScopeHierName(ctx), stmt->range.start.line,
      stmt->cover_sequence ? CoverStatementCategory::kSequence
                           : CoverStatementCategory::kProperty);
}

// §16.14.3: one verdict of a concurrent cover's attempt counted in its
// results: a cover sequence's match, with multiplicity, or a cover
// property's success, at most once per attempt and apart where it is by
// vacuity; a verdict that does not hold counts nothing, and a disabled
// attempt reaches none. Nothing for any other assertion.
void RecordConcurrentCoverVerdict(const Stmt* stmt,
                                  const PropertyVerdict& verdict,
                                  SimContext& ctx) {
  ConcurrentCoverResult* record = ConcurrentCoverRecord(stmt, ctx);
  if (record == nullptr || !verdict.holds) return;
  if (stmt->cover_sequence) {
    // The evaluation drops an attempt at the tick the disable condition is
    // true at, so a match that reaches a verdict completed without it.
    record->matched +=
        CoverSequenceMatchDelta({/*disable_iff_occurred=*/false});
    return;
  }
  CoverPropertyAttemptOutcome outcome;
  outcome.nonvacuous_success = !verdict.vacuous;
  outcome.vacuous_success = verdict.vacuous;
  record->succeeded += CoverPropertySuccessDelta(outcome);
  record->vacuous += CoverPropertyVacuousSuccessDelta(outcome);
}

// The key of the assertion `stmt` the current process is evaluating. A
// labelled statement runs inside its label's own named scope (§21.2.1.5),
// which is the assertion's name rather than a scope it is written in, so that
// level is left out.
std::string KeyHere(const Stmt* stmt, SimContext& ctx) {
  std::string scope = ScopeHierName(ctx);
  const std::vector<std::string_view>& named = ctx.ActiveNamedScopes();
  if (!stmt->label.empty() && !named.empty() && named.back() == stmt->label &&
      scope.size() > stmt->label.size()) {
    scope.resize(scope.size() - stmt->label.size() - 1);
  }
  return RunAssertionKey(stmt, scope, ctx);
}

// §40.2.2 with §40.5.2: one `outcome` of the assertion `stmt` the current
// process evaluates, counted for its coverage; nothing is looked up for a
// statement no instance counts.
void NoteCoverageHere(const Stmt* stmt, AssertionOutcome outcome,
                      SimContext& ctx) {
  CoverageControlState& cov = ctx.GetCoverageControlState();
  if (!cov.Code().assertions.contains(stmt)) return;
  NoteAssertionOutcome(
      stmt, CoverageInstancePrefix(ctx.ActiveInstancePrefix()), outcome, 1,
      [&] { return KeyHere(stmt, ctx); }, cov);
}

// §39.4.2: calls each `reason` callback placed on the assertion `stmt`,
// handed `info`; nothing is looked up where no callback is placed at all.
void RaiseAttemptEvent(const Stmt* stmt, int reason,
                       const AssertionAttemptInfo& info, SimContext& ctx) {
  AssertionApi& api = GetGlobalAssertionApi();
  if (api.PlacedCallbackCount() == 0) return;
  api.DeliverAssertionEvent(KeyHere(stmt, ctx), reason, ctx.CurrentTime().ticks,
                            info);
}

// §39.4.2.1: waits for the tick of `gclk_event` strictly after
// `event_time`, then calls the `reason` control callbacks placed on the
// assertion `key` with cb_time `event_time`.
SimCoroutine DeferredControlCallback(std::string key, int reason,
                                     uint64_t event_time,
                                     const std::vector<EventExpr>& gclk_event,
                                     SimContext& ctx) {
  do {
    co_await EventAwaiter{ctx, gclk_event, ctx.GetArena()};
  } while (ctx.CurrentTime().ticks <= event_time);
  GetGlobalAssertionApi().DeliverAssertionEvent(key, reason, event_time, {});
}

// §16.9.4: the process asserting the assertion the API keeps under `key`
// where its property names a global clocking future sampled value function,
// the one process carrying a global clocking event that was started from that
// assertion; null for every other assertion.
const Process* FutureGclkAsserting(std::string_view key, SimContext& ctx) {
  for (const Process* proc : ctx.GetScheduler().Threads()) {
    if (proc->gclk_future_event.empty() || proc->origin == nullptr) continue;
    if (RunAssertionKey(proc->origin, ProcessHierName(*proc, ctx), ctx) ==
        key) {
      return proc;
    }
  }
  return nullptr;
}

// The attempt information of the attempt begun at `started`, in ticks.
AssertionAttemptInfo AttemptBegunAt(uint64_t started) {
  AssertionAttemptInfo info;
  info.attempt_start_time = started;
  return info;
}

// The source text of `expr`, the name the model keeps an expression by; empty
// for none.
std::string TextOf(const Expr* expr) {
  return expr != nullptr ? VpiExprDecompile(expr) : std::string();
}

// The operand an attempt failed at among `reads`, what it read at one tick:
// the last it read false, else the last it read; null where it read none.
const OperandRead* FailedRead(const AttemptLog& reads) {
  const OperandRead* last = nullptr;
  for (auto read = reads.rbegin(); read != reads.rend(); ++read) {
    if ((*read)->expr == nullptr) continue;
    if (!(*read)->held) return *read;
    if (last == nullptr) last = *read;
  }
  return last;
}

// The reads of each attempt in `log`, in the order the attempts were
// stepped, each led by the note of its step.
std::vector<AttemptLog> AttemptsIn(const std::vector<OperandRead>& log) {
  std::vector<AttemptLog> attempts;
  for (const OperandRead& read : log) {
    if (read.expr == nullptr) attempts.emplace_back();
    if (!attempts.empty()) attempts.back().push_back(&read);
  }
  return attempts;
}

// The verdict among `decided` of the attempt begun at `started`, null where
// it was decided at no verdict this tick; a failure is given the operand it
// failed at, `failed`, where one is known.
const PropertyVerdict* DecisionOf(std::vector<PropertyVerdict>& decided,
                                  uint64_t started, const OperandRead* failed) {
  PropertyVerdict* verdict = nullptr;
  for (PropertyVerdict& decision : decided) {
    if (decision.started == started) verdict = &decision;
  }
  if (verdict != nullptr && !verdict->holds && failed != nullptr) {
    verdict->failed_at = failed->expr;
  }
  return verdict;
}

}  // namespace

std::string RunAssertionKey(const Stmt* stmt, std::string_view scope,
                            SimContext& ctx) {
  const SourceLoc kStart =
      ctx.GetDiag().Sources().ResolveToOrigin(stmt->range.start);
  return AssertionKey(scope, stmt->label, kStart.line, kStart.column);
}

void NoteAttemptBegun(const Stmt* stmt, SimContext& ctx) {
  NoteCoverageHere(stmt, AssertionOutcome::kAttempt, ctx);
  if (ConcurrentCoverResult* record = ConcurrentCoverRecord(stmt, ctx)) {
    record->attempted += stmt->cover_sequence
                             ? CoverSequenceAttemptDelta()
                             : CoverPropertyAttemptDelta(/*outcome=*/{});
  }
  AssertionApi& api = GetGlobalAssertionApi();
  if (api.PlacedCallbackCount() == 0) return;
  // §39.5.2: stepping enabled for the attempt before it began is frozen now.
  const uint64_t kNow = ctx.CurrentTime().ticks;
  const std::string kKey = KeyHere(stmt, ctx);
  if (api.AssertionStepEnabled(kKey, kNow)) {
    api.NoteAssertionAttemptStarted(kKey, kNow);
  }
  RaiseAttemptEvent(stmt, cbAssertionStart, AttemptBegunAt(kNow), ctx);
}

void NoteAttemptVerdict(const Stmt* stmt, const PropertyVerdict& verdict,
                        SimContext& ctx) {
  RecordConcurrentCoverVerdict(stmt, verdict, ctx);
  AssertionAttemptInfo info = AttemptBegunAt(verdict.started);
  int reason = cbAssertionFailure;
  AssertionOutcome outcome = AssertionOutcome::kFailure;
  if (verdict.holds) {
    reason = verdict.vacuous ? cbAssertionVacuousSuccess : cbAssertionSuccess;
    outcome = verdict.vacuous ? AssertionOutcome::kVacuousSuccess
                              : AssertionOutcome::kSuccess;
  } else {
    info.fail_expr = TextOf(verdict.failed_at);
  }
  NoteCoverageHere(stmt, outcome, ctx);
  RaiseAttemptEvent(stmt, reason, info, ctx);
}

void NoteAttemptDisabled(const Stmt* stmt, uint64_t started, SimContext& ctx) {
  NoteCoverageHere(stmt, AssertionOutcome::kDisabled, ctx);
  RaiseAttemptEvent(stmt, cbAssertionDisabledEvaluation,
                    AttemptBegunAt(started), ctx);
}

void NoteAttemptsKilled(const Stmt* stmt, const Process& proc,
                        std::size_t killed, SimContext& ctx) {
  NoteAssertionOutcome(
      stmt, CoverageInstancePrefix(proc.inst_prefix), AssertionOutcome::kKilled,
      killed, [] { return std::string(); }, ctx.GetCoverageControlState());
}

void AbortAttemptStartedAt(std::string_view key, uint64_t started,
                           SimContext& ctx) {
  for (Process* proc : ctx.GetScheduler().Threads()) {
    const std::string kScope = ProcessHierName(*proc, ctx);
    auto keyed = [&](const Stmt* stmt) {
      return RunAssertionKey(stmt, kScope, ctx) == key;
    };
    for (auto& [stmt, state] : proc->property_tree_states) {
      if (state != nullptr && keyed(stmt)) {
        NoteAttemptsKilled(stmt, *proc,
                           AbortPropertyTreeAttemptAt(*state, started), ctx);
      }
    }
    for (auto& [stmt, state] : proc->sequence_property_states) {
      if (state != nullptr && keyed(stmt)) {
        NoteAttemptsKilled(
            stmt, *proc, AbortSequencePropertyAttemptAt(*state, started), ctx);
      }
    }
  }
}

void RaiseAssertionControlCallback(std::string_view key, int reason,
                                   SimContext& ctx) {
  const uint64_t kNow = ctx.CurrentTime().ticks;
  const Process* asserting = FutureGclkAsserting(key, ctx);
  if (asserting == nullptr) {
    GetGlobalAssertionApi().DeliverAssertionEvent(key, reason, kNow, {});
    return;
  }
  Process* p =
      CreateAssertionChildProcess(ctx, ctx.GetArena(), Region::kActive);
  // The event is the asserting instance's, whichever process controlled it.
  p->inst_prefix = asserting->inst_prefix;
  p->gen_prefixes = asserting->gen_prefixes;
  p->gen_block_name = asserting->gen_block_name;
  p->coro = DeferredControlCallback(std::string(key), reason, kNow,
                                    asserting->gclk_future_event, ctx)
                .Release();
  ScheduleAssertionChildStart(p, p->home_region, ctx);
}

AttemptReads::AttemptReads(const Stmt* stmt, SimContext& ctx)
    : stmt_(stmt), ctx_(ctx) {
  logging_ = GetGlobalAssertionApi().PlacedCallbackCount() != 0;
  if (logging_) ctx_.AssertionSamples().SetOperandLog(&log_);
}

AttemptReads::~AttemptReads() {
  if (logging_) ctx_.AssertionSamples().SetOperandLog(nullptr);
}

void AttemptReads::Finish(std::vector<PropertyVerdict>& decided) {
  if (!logging_) return;
  ctx_.AssertionSamples().SetOperandLog(nullptr);
  logging_ = false;
  for (const AttemptLog& reads : AttemptsIn(log_)) {
    const OperandRead* failed = FailedRead(reads);
    Step(reads, DecisionOf(decided, reads.front()->started, failed), failed);
  }
}

void AttemptReads::Step(const AttemptLog& reads, const PropertyVerdict* verdict,
                        const OperandRead* failed) {
  const uint64_t kStarted = reads.front()->started;
  const uint32_t kStep =
      GetGlobalAssertionApi().TakeAttemptStep(KeyHere(stmt_, ctx_), kStarted);
  if (kStep == AssertionApi::kNoStep) return;
  const bool kFails = verdict != nullptr && !verdict->holds;
  AssertionAttemptInfo info = AttemptBegunAt(kStarted);
  for (const OperandRead* read : reads) {
    if (read->expr != nullptr && read->held) {
      info.step.matched_exprs.push_back(TextOf(read->expr));
    }
  }
  if (kFails && failed != nullptr && !failed->held) {
    info.step.matched_exprs.push_back(TextOf(failed->expr));
  }
  info.step.state_from = kStep == 0 ? 0 : static_cast<int>(kStep) + 1;
  info.step.state_to = static_cast<int>(kStep) + 2;
  if (verdict != nullptr)
    info.step.state_to = kFails ? info.step.state_from : 1;
  RaiseAttemptEvent(stmt_,
                    kFails ? cbAssertionStepFailure : cbAssertionStepSuccess,
                    info, ctx_);
}

}  // namespace delta
