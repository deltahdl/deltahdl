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
#include "simulator/stmt_exec.h"
#include "simulator/stmt_exec_internal.h"
#include "simulator/sva_engine.h"

namespace delta {

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

ExecTask ExecImmediateAssert(const Stmt* stmt, SimContext& ctx, Arena& arena) {
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

// §16.4.5: a deferred immediate assertion may be written inside a function, and
// that function may be called by several different processes. Because a
// synchronous subroutine call does not change SimContext::CurrentProcess(), the
// assertion runs in the context of whichever process called the function, so
// its report is queued against that process's own pending-report generation
// (see §16.4.1/§16.4.2) and matures or is flushed independently of the other
// callers -- each process execution is independent.
//
// The function-body executor (ExecFuncStmt) is synchronous and cannot co_await,
// but a deferred assertion never runs its action inline: it only evaluates its
// expression and schedules the pass/fail report into a later region. That work
// is entirely synchronous, so it is exposed here for ExecFuncStmt to invoke.
// This mirrors the deferred branches of ExecImmediateAssert; the simple
// immediate (non-deferred) case is outside this subclause and not handled here.
void ExecDeferredImmediateAssertInFunction(const Stmt* stmt, SimContext& ctx,
                                           Arena& arena) {
  uint32_t type_bit = ImmediateAssertionTypeBit(stmt);
  uint32_t directive_bit = ImmediateDirectiveTypeBit(stmt);
  if (!ctx.AssertCheckingEnabled(type_bit, directive_bit)) return;

  auto cond = EvalExpr(stmt->assert_expr, ctx, arena);
  bool is_true = cond.IsTruthy();
  RecordCoverImmediateSample(stmt, is_true, ctx);
  if (is_true) {
    if (stmt->assert_pass_stmt) {
      ScheduleDeferredAction(stmt->assert_pass_stmt, stmt->is_final_deferred,
                             stmt->label, ctx, arena);
    }
  } else if (stmt->assert_fail_stmt) {
    ScheduleDeferredAction(stmt->assert_fail_stmt, stmt->is_final_deferred,
                           stmt->label, ctx, arena);
  } else if (stmt->kind != StmtKind::kCoverImmediate) {
    // §20.11: the failure is counted even when its report action is suppressed.
    ctx.IncrementAssertionFailCount();
    if (ctx.AssertFailActionEnabled(type_bit, directive_bit)) {
      // §16.4.1: the default $error is a pending report scheduled with the
      // calling process's other deferred reports, not emitted here.
      ScheduleDeferredSeverityReport(stmt->is_final_deferred, stmt->label, ctx);
    }
  }
}

}  // namespace delta
