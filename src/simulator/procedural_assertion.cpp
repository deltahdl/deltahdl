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

void CollectQueuedAssertions(const Stmt* s, std::vector<const Stmt*>& out) {
  if (s == nullptr) return;
  if (s->is_procedural_concurrent && s->is_concurrent_clocked &&
      !s->assert_clock.empty() && s->kind != StmtKind::kExpect) {
    out.push_back(s);
  }
  ForEachChildStmt(
      s, [&out](Stmt* const& sub) { CollectQueuedAssertions(sub, out); });
}

void TickInstances(ProceduralAssertionState* state,
                   const AttemptInstances& instances, SimContext& ctx,
                   Arena& arena) {
  std::vector<std::string_view> saved = ctx.ActiveNamedScopes();
  PendingReportScope::Replace(ctx, state->named_scopes);
  ExecConcurrentAssertionTick(state->stmt, instances, ctx, arena);
  PendingReportScope::Replace(ctx, saved);
}

SimCoroutine MonitorCoroutine(const Stmt* stmt, ProceduralAssertionState* state,
                              SimContext& ctx, Arena& arena) {
  for (;;) {
    co_await EventAwaiter{ctx, stmt->assert_clock, arena};
    co_await RegionAwaiter{ctx, Region::kObserved};
    state->ticked_at = ctx.CurrentTime().ticks;
    if (!state->reached) continue;
    AttemptInstances instances = std::move(state->matured);
    state->matured.clear();
    instances.insert(instances.end(), state->pending.begin(),
                     state->pending.end());
    state->pending.clear();
    TickInstances(state, instances, ctx, arena);
  }
}

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

ProceduralAssertionState* StartMonitor(const Stmt* stmt,
                                       std::string_view inst_prefix,
                                       SimContext& ctx, Arena& arena) {
  auto* state = arena.Create<ProceduralAssertionState>();
  state->stmt = stmt;
  auto* monitor = CreateAssertionChildProcess(ctx, arena, Region::kActive);
  monitor->inst_prefix = inst_prefix;
  monitor->is_concurrent_clocked = true;
  state->monitor = monitor;
  monitor->coro = MonitorCoroutine(stmt, state, ctx, arena).Release();
  ScheduleAssertionChildStart(monitor, Region::kActive, ctx);
  return state;
}

void PlaceInstance(ProceduralAssertionState* state,
                   const InstanceBindings* bindings, SimContext& ctx,
                   Arena& arena) {
  if (!state->reached) {
    state->reached = true;
    state->named_scopes = ctx.ActiveNamedScopes();
  }
  state->pending.push_back(bindings);
  ScheduleMaturing(state, ctx, arena);
}

}  // namespace

void StartProceduralAssertionMonitors(Process* proc, const Stmt* body,
                                      SimContext& ctx, Arena& arena) {
  std::vector<const Stmt*> statements;
  CollectQueuedAssertions(body, statements);
  for (const Stmt* stmt : statements) {
    ProceduralAssertionState* state =
        StartMonitor(stmt, proc->inst_prefix, ctx, arena);
    proc->procedural_assertions[stmt] = state;
    state->monitor->gen_prefixes = proc->gen_prefixes;
    state->monitor->gen_block_name = proc->gen_block_name;
    state->monitor->program_block_id = proc->program_block_id;
  }
}

const ProceduralCheckerAssertion* StartProceduralCheckerAssertion(
    const Stmt* stmt, std::string_view inst_prefix,
    std::vector<const Expr*> saved_actuals, SimContext& ctx, Arena& arena) {
  auto* assertion = arena.Create<ProceduralCheckerAssertion>();
  assertion->stmt = stmt;
  assertion->inst_prefix = inst_prefix;
  assertion->saved_actuals = std::move(saved_actuals);
  if (stmt->is_concurrent_clocked) {
    assertion->state = StartMonitor(stmt, inst_prefix, ctx, arena);
  }
  return assertion;
}

bool EnqueueProceduralAssertion(const Stmt* stmt, SimContext& ctx,
                                Arena& arena) {
  Process* proc = ctx.CurrentProcess();
  if (proc == nullptr) return false;
  auto it = proc->procedural_assertions.find(stmt);
  if (it == proc->procedural_assertions.end()) return false;
  PlaceInstance(it->second, CaptureInstanceBindings(stmt, ctx, arena), ctx,
                arena);
  return true;
}

void EnqueueProceduralCheckerAssertion(
    const ProceduralCheckerAssertion& assertion, SimContext& ctx,
    Arena& arena) {
  ctx.CurrentProcess()->procedural_assertions.emplace(assertion.stmt,
                                                      assertion.state);
  auto* bindings = arena.Create<InstanceBindings>();
  for (const Expr* actual : assertion.saved_actuals) {
    BindSites(actual, *bindings, ctx, arena);
  }
  PlaceInstance(assertion.state, bindings->values.empty() ? nullptr : bindings,
                ctx, arena);
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
