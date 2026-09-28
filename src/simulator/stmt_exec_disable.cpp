// §9.6.2's disable statement and §9.6.3's disable fork: ending a named block,
// a labeled statement, a task or a fork, in the process issuing the disable or
// in another, and ending the processes a process spawned. Also §16.4.4's and
// §16.14.6.4's flush of the deferred and procedural assertion queues a disable
// of a procedure's outermost scope, or of one assertion, brings with it.

#include <algorithm>
#include <coroutine>
#include <string>
#include <string_view>
#include <vector>

#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/exec_task.h"
#include "simulator/procedural_assertion.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/stmt_exec_internal.h"
#include "simulator/stmt_result.h"

namespace delta {

// §16.4.4: a disable of the outermost scope of a procedure holding a deferred
// assertion queue flushes that queue beside §9.6.2's own activities, whether
// or not the block is executing -- the clause's own example disables b2 from
// another always block while b2 sits on its event control -- so the outermost
// scope is looked up on its own rather than among the blocks a process is
// inside. The queue alone is touched: §9.6.2 leaves a block that is not
// executing unaffected, so the process keeps running. §16.14.6.4 has the same
// disable flush the procedure's procedural assertion queue, its matured
// attempts untouched, the procedure disabling its own outermost scope flushing
// its own. Answers whether the target named any procedure's outermost scope,
// so that a name answered here is not also taken for an assertion label.
static bool FlushDeferredQueueOfOutermostScope(std::string_view target,
                                               const Process* current,
                                               SimContext& ctx) {
  const auto& procs = ctx.FindOutermostScopeProcesses(target);
  for (auto* proc : procs) {
    FlushProceduralAssertionQueue(*proc);
    if (proc == current) continue;
    proc->deferred_report_generation++;
  }
  return !procs.empty();
}

// §9.6.2: the label a disable names -- the name itself, or the last name of a
// hierarchical one, `t.counter.cnt`, the block the named-scope registry holds
// under its own label.
static std::string_view DisableTargetLabel(const Expr* e) {
  while (e != nullptr && e->kind == ExprKind::kMemberAccess &&
         !e->is_scope_resolution) {
    e = e->rhs;
  }
  return e != nullptr && e->kind == ExprKind::kIdentifier ? e->text
                                                          : std::string_view{};
}

// §9.6.2: a disable from another process of a block, a labeled statement or a
// task that `proc` itself stands in ends it where the process waits, and the
// process goes on after it. The wait is abandoned -- its gate closed, so its
// own wake resumes nothing -- and the statement waiting answers kDisable to
// the one around it, which unwinds to the scope named as a disable the process
// issued itself does. False where the process waits in no wait it can be
// taken out of, which leaves it to be killed.
static bool TryUnwindForDisable(Process* proc, std::string_view target,
                                SimContext& ctx) {
  const auto& scopes = proc->saved_named_scopes;
  if (std::find(scopes.begin(), scopes.end(), target) == scopes.end()) {
    return false;
  }
  ParkSlot& park = proc->park;
  if (!park.frame || !park.gate || !park.frame.promise().continuation) {
    return false;
  }
  park.gate->open = false;
  auto frame = park.frame;
  park.frame = {};
  park.gate.reset();
  frame.promise().result = StmtResult::kDisable;
  std::coroutine_handle<> cont = frame.promise().continuation;
  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  event->callback = [proc, cont, target, &ctx]() {
    if (!proc->active) return;
    ctx.SetCurrentProcess(proc);
    ctx.SetDisableTarget(target);
    cont.resume();
  };
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), Region::kActive, event);
  return true;
}

StmtResult ExecDisableImpl(const Stmt* stmt, SimContext& ctx) {
  auto target = DisableTargetLabel(stmt->expr);
  if (target.empty()) return StmtResult::kDone;

  auto* current = ctx.CurrentProcess();

  auto procs = ctx.FindNamedScopeProcesses(target);
  std::sort(procs.begin(), procs.end());
  procs.erase(std::unique(procs.begin(), procs.end()), procs.end());
  bool self_disable = false;

  for (auto* proc : procs) {
    if (proc == current) {
      self_disable = true;
      continue;
    }
    if (TryUnwindForDisable(proc, target, ctx)) continue;

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

  bool named_a_procedure_scope =
      FlushDeferredQueueOfOutermostScope(target, current, ctx);

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
  if (procs.empty() && !named_a_procedure_scope && current) {
    current->cancelled_deferred_labels.insert(std::string(target));
    // §16.14.6.4: or a specific procedural concurrent assertion, whose
    // pending instances alone are cleared.
    DisableProceduralAssertion(*current, target);
  }

  return StmtResult::kDone;
}

static void DisableDescendants(Process* proc) {
  for (auto* child : proc->children) {
    child->active = false;
    DisableDescendants(child);
  }
}

StmtResult ExecDisableForkImpl(SimContext& ctx) {
  auto* proc = ctx.CurrentProcess();
  if (!proc) return StmtResult::kDone;
  DisableDescendants(proc);
  proc->wait_fork_state.remaining = 0;
  proc->children.clear();
  return StmtResult::kDone;
}

}  // namespace delta
