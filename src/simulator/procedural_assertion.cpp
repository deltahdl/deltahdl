#include "simulator/procedural_assertion.h"

#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/sensitivity.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "simulator/awaiters_event_control.h"
#include "simulator/evaluation.h"
#include "simulator/expr_walk.h"
#include "simulator/instance_bindings.h"
#include "simulator/process.h"
#include "simulator/property_attempts.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/stmt_exec_assertion_internal.h"
#include "simulator/sva_engine_sampling.h"

namespace delta {

namespace {

// The concurrent assertions embedded in `s` that carry a leading clocking
// event, those in the action block of another among them; not §16.17's
// expect, which blocks the process on its property rather than queueing
// an instance.
void CollectQueuedAssertions(const Stmt* s, std::vector<const Stmt*>& out) {
  if (s == nullptr) return;
  if (s->is_procedural_concurrent && s->is_concurrent_clocked &&
      !s->assert_clock.empty() && s->kind != StmtKind::kExpect) {
    out.push_back(s);
  }
  ForEachChildStmt(
      s, [&out](Stmt* const& sub) { CollectQueuedAssertions(sub, out); });
}

// One tick of the statement in the monitor's process, the current one,
// beginning an attempt per instance given, the statement's reports naming
// the scopes the procedure reached it in.
void TickInstances(ProceduralAssertionState* state,
                   const AttemptInstances& instances, SimContext& ctx,
                   Arena& arena) {
  std::vector<std::string_view> saved = ctx.ActiveNamedScopes();
  PendingReportScope::Replace(ctx, state->named_scopes);
  ExecConcurrentAssertionTick(state->stmt, instances, ctx, arena);
  PendingReportScope::Replace(ctx, saved);
}

// §16.14.6: the life of one statement's monitor: at every occurrence of the
// leading clocking event, in the Observed region, the attempts in flight
// advance and one begins per pending instance. A tick before the statement
// was ever reached has nothing in flight and nothing to begin.
SimCoroutine MonitorCoroutine(const Stmt* stmt, ProceduralAssertionState* state,
                              SimContext& ctx, Arena& arena) {
  for (;;) {
    co_await EventAwaiter{ctx, stmt->assert_clock, arena};
    co_await RegionAwaiter{ctx, Region::kObserved};
    state->ticked_at = ctx.CurrentTime().ticks;
    if (!state->reached) continue;
    // The instances matured in earlier steps and the ones pending in this,
    // which mature in this Observed region, all begin an attempt.
    AttemptInstances instances = std::move(state->matured);
    state->matured.clear();
    instances.insert(instances.end(), state->pending.begin(),
                     state->pending.end());
    state->pending.clear();
    TickInstances(state, instances, ctx, arena);
  }
}

// §16.14.6.1: the sites of `e` whose value the instance saves as it is
// queued, a const cast's operand read as it stands and an automatic
// variable, one the process keeps in a scope of its own, read likewise; a
// static variable is left to §16.5.1's sampling at each tick.
void BindSites(const Expr* e, InstanceBindings& out, SimContext& ctx,
               Arena& arena) {
  ForEachSubExpr(e, [&](const Expr* sub) {
    bool constant = sub->kind == ExprKind::kCast && sub->text == "const";
    bool automatic = sub->kind == ExprKind::kIdentifier &&
                     ctx.FindLocalVariable(sub->text) != nullptr;
    if (!constant && !automatic) return;
    Logic4Vec value = EvalExpr(constant ? sub->lhs : sub, ctx, arena);
    out.values.emplace_back(sub,
                            AssertionSampleStore::OwnedSample(value, arena));
  });
}

// The sites of a sequence body: its operands and those of the bodies it
// intersects, conjoins and alternates with.
void BindSequenceSites(const SeqLinearBody& body, InstanceBindings& out,
                       SimContext& ctx, Arena& arena) {
  for (const Expr* operand : body.operands) BindSites(operand, out, ctx, arena);
  for (const SeqLinearBody& sub : body.intersects) {
    BindSequenceSites(sub, out, ctx, arena);
  }
  for (const SeqLinearBody& sub : body.conjuncts) {
    BindSequenceSites(sub, out, ctx, arena);
  }
  for (const SeqLinearBody& sub : body.alternatives) {
    BindSequenceSites(sub, out, ctx, arena);
  }
}

// The sites of a property tree: each node's boolean and sequence.
void BindTreeSites(const PropertyExprNode* node, InstanceBindings& out,
                   SimContext& ctx, Arena& arena) {
  if (node == nullptr) return;
  BindSites(node->boolean, out, ctx, arena);
  if (node->sequence != nullptr) {
    BindSequenceSites(node->sequence->seq_linear, out, ctx, arena);
  }
  for (const PropertyExprNode* operand : node->operands) {
    BindTreeSites(operand, out, ctx, arena);
  }
}

// §16.14.6.1: what one instance of `stmt` saves as it is queued: the sites
// of its property, its disable condition and its action block, whose
// variables the same rules apply to.
const InstanceBindings* CaptureInstanceBindings(const Stmt* stmt,
                                                SimContext& ctx, Arena& arena) {
  auto* bindings = arena.Create<InstanceBindings>();
  BindSites(stmt->assert_expr, *bindings, ctx, arena);
  BindSites(stmt->assert_disable_iff, *bindings, ctx, arena);
  BindTreeSites(stmt->assert_property, *bindings, ctx, arena);
  if (stmt->assert_sequence != nullptr) {
    BindSequenceSites(stmt->assert_sequence->seq_linear, *bindings, ctx, arena);
  }
  auto bind = [&](const Expr* e) { BindSites(e, *bindings, ctx, arena); };
  ForEachStmtReadExpr(stmt->assert_pass_stmt, bind);
  ForEachStmtReadExpr(stmt->assert_fail_stmt, bind);
  return bindings->values.empty() ? nullptr : bindings;
}

// §16.14.6: each pending instance matures in the Observed region of the
// time step it was queued in, whether or not the step holds a tick of the
// statement's clock; one maturing is scheduled per step per statement, the
// first enqueue of the step scheduling it, and it moves what is pending by
// then, what §16.14.6.2's flush points left, to the matured queue.
// §16.14.6.3: where the clock ticked earlier in the step, the monitor
// having run in an earlier pass of the Observed region, the instances
// begin their attempts here and then, in the monitor's process.
void ScheduleMaturing(ProceduralAssertionState* state, SimContext& ctx,
                      Arena& arena) {
  if (state->maturing_scheduled) return;
  state->maturing_scheduled = true;
  auto* ev = ctx.GetScheduler().GetEventPool().Acquire();
  ev->callback = [state, &ctx, &arena]() {
    state->maturing_scheduled = false;
    if (state->pending.empty()) return;
    if (state->ticked_at != ctx.CurrentTime().ticks) {
      state->matured.insert(state->matured.end(), state->pending.begin(),
                            state->pending.end());
      state->pending.clear();
      return;
    }
    AttemptInstances instances = std::move(state->pending);
    state->pending.clear();
    Process* saved = ctx.CurrentProcess();
    ctx.SetCurrentProcess(state->monitor);
    TickInstances(state, instances, ctx, arena);
    ctx.SetCurrentProcess(saved);
  };
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), Region::kObserved, ev);
}

}  // namespace

void StartProceduralAssertionMonitors(Process* proc, const Stmt* body,
                                      SimContext& ctx, Arena& arena) {
  std::vector<const Stmt*> statements;
  CollectQueuedAssertions(body, statements);
  for (const Stmt* stmt : statements) {
    auto* state = arena.Create<ProceduralAssertionState>();
    state->stmt = stmt;
    proc->procedural_assertions[stmt] = state;
    // The monitor stands in the procedure's instance and generate blocks, as
    // the attempt of a static assertion stands in its process's, and it is
    // marked as carrying a concurrent assertion so that its wake at the
    // clocking event lands in the Observed region.
    auto* monitor = CreateAssertionChildProcess(ctx, arena, Region::kActive);
    monitor->inst_prefix = proc->inst_prefix;
    monitor->gen_prefixes = proc->gen_prefixes;
    monitor->gen_block_name = proc->gen_block_name;
    monitor->program_block_id = proc->program_block_id;
    monitor->is_concurrent_clocked = true;
    state->monitor = monitor;
    monitor->coro = MonitorCoroutine(stmt, state, ctx, arena).Release();
    ScheduleAssertionChildStart(monitor, Region::kActive, ctx);
  }
}

bool EnqueueProceduralAssertion(const Stmt* stmt, SimContext& ctx,
                                Arena& arena) {
  Process* proc = ctx.CurrentProcess();
  if (proc == nullptr) return false;
  auto it = proc->procedural_assertions.find(stmt);
  if (it == proc->procedural_assertions.end()) return false;
  ProceduralAssertionState* state = it->second;
  if (!state->reached) {
    state->reached = true;
    state->named_scopes = ctx.ActiveNamedScopes();
  }
  state->pending.push_back(CaptureInstanceBindings(stmt, ctx, arena));
  ScheduleMaturing(state, ctx, arena);
  return true;
}

void FlushProceduralAssertionQueue(Process& proc) {
  for (auto& entry : proc.procedural_assertions) {
    entry.second->pending.clear();
  }
}

bool DisableProceduralAssertion(Process& proc, std::string_view label) {
  bool named = false;
  for (auto& entry : proc.procedural_assertions) {
    if (entry.first->label != label) continue;
    entry.second->pending.clear();
    named = true;
  }
  return named;
}

}  // namespace delta
