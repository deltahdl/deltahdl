#include "simulator/procedural_assertion.h"

#include <cstdint>
#include <vector>

#include "common/arena.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast.h"
#include "simulator/awaiters_event_control.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/stmt_exec_assertion_internal.h"

namespace delta {

namespace {

// The concurrent assertions embedded in `s` that carry a leading clocking
// event, those in the action block of another among them.
void CollectQueuedAssertions(const Stmt* s, std::vector<const Stmt*>& out) {
  if (s == nullptr) return;
  if (s->is_procedural_concurrent && s->is_concurrent_clocked &&
      !s->assert_clock.empty()) {
    out.push_back(s);
  }
  ForEachChildStmt(
      s, [&out](Stmt* const& sub) { CollectQueuedAssertions(sub, out); });
}

// §16.14.6: the life of one statement's monitor: at every occurrence of the
// leading clocking event, in the Observed region, the attempts in flight
// advance and one begins per pending instance, the statement's reports
// naming the scopes the procedure reached it in. A tick before the
// statement was ever reached has nothing in flight and nothing to begin.
SimCoroutine MonitorCoroutine(const Stmt* stmt, ProceduralAssertionState* state,
                              SimContext& ctx, Arena& arena) {
  for (;;) {
    co_await EventAwaiter{ctx, stmt->assert_clock, arena};
    co_await ObservedRegionAwaiter{ctx};
    if (!state->reached) continue;
    uint32_t begin = state->pending;
    state->pending = 0;
    std::vector<std::string_view> saved = ctx.ActiveNamedScopes();
    PendingReportScope::Replace(ctx, state->named_scopes);
    ExecConcurrentAssertionTick(stmt, begin, ctx, arena);
    PendingReportScope::Replace(ctx, saved);
  }
}

}  // namespace

void StartProceduralAssertionMonitors(Process* proc, const Stmt* body,
                                      SimContext& ctx, Arena& arena) {
  std::vector<const Stmt*> statements;
  CollectQueuedAssertions(body, statements);
  for (const Stmt* stmt : statements) {
    auto* state = arena.Create<ProceduralAssertionState>();
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
    monitor->coro = MonitorCoroutine(stmt, state, ctx, arena).Release();
    ScheduleAssertionChildStart(monitor, Region::kActive, ctx);
  }
}

bool EnqueueProceduralAssertion(const Stmt* stmt, SimContext& ctx) {
  Process* proc = ctx.CurrentProcess();
  if (proc == nullptr) return false;
  auto it = proc->procedural_assertions.find(stmt);
  if (it == proc->procedural_assertions.end()) return false;
  ProceduralAssertionState* state = it->second;
  if (!state->reached) {
    state->reached = true;
    state->named_scopes = ctx.ActiveNamedScopes();
  }
  ++state->pending;
  return true;
}

}  // namespace delta
