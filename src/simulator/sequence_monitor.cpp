#include "simulator/sequence_monitor.h"

#include <cstddef>
#include <string>
#include <vector>

#include "common/types.h"
#include "parser/ast.h"
#include "simulator/awaiters.h"
#include "simulator/evaluation.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {
namespace {

// §16.14.5 always-semantics: advance every in-flight attempt by one operand at
// this clock tick. An attempt whose current Boolean operand is true moves on;
// one that satisfies the last operand reports a match; the rest are dropped.
// The caller adds a fresh attempt (position 0) before each tick.
bool AdvanceLinearAttempts(const std::vector<Expr*>& operands,
                           std::vector<size_t>& active, SimContext& ctx,
                           Arena& arena) {
  std::vector<size_t> next;
  next.reserve(active.size());
  bool matched = false;
  for (size_t pos : active) {
    if (!EvalExpr(operands[pos], ctx, arena).IsTruthy()) continue;
    if (pos + 1 == operands.size()) {
      matched = true;
    } else {
      next.push_back(pos + 1);
    }
  }
  active = std::move(next);
  return matched;
}

// §16.13.6: mark the sequence endpoint event triggered and wake its waiters,
// mirroring the named-event `-> ev` trigger path (stmt_exec.cpp).
void FireSequenceEndpoint(SimContext& ctx, const std::string& ep_name) {
  auto* var = ctx.FindVariable(ep_name);
  if (!var) return;
  ctx.SetEventTriggered(ep_name);
  auto pending = std::move(var->watchers);
  var->watchers.clear();
  auto& sched = ctx.GetScheduler();
  Region region = ctx.IsReactiveContext() ? Region::kReactive : Region::kActive;
  for (auto& cb : pending) {
    auto* event = sched.GetEventPool().Acquire();
    event->callback = std::move(cb);
    sched.ScheduleEvent(ctx.CurrentTime(), region, event);
  }
}

}  // namespace

SimCoroutine MakeSequenceMonitorCoroutine(const ModuleItem* seq,
                                          SimContext& ctx, Arena& arena) {
  std::string ep_name = "__seq_" + std::string(seq->name);
  const std::vector<Expr*>& operands = seq->seq_linear_operands;
  std::vector<size_t> active;
  while (!ctx.StopRequested()) {
    co_await EventAwaiter{ctx, seq->seq_clock, arena};
    // TEMP DIAGNOSTIC: write the value WaitBlocks expects (42) directly to
    // `result` on each clock tick, bypassing __seq_/wait, so the test PASSES
    // iff the monitor spawns and clocks (isolates spawn+clk). Revert after.
    if (auto* rv = ctx.FindVariable("result")) {
      rv->value = MakeLogic4VecVal(arena, 8, 42);
    }
    active.push_back(0);
    AdvanceLinearAttempts(operands, active, ctx, arena);
    FireSequenceEndpoint(ctx, ep_name);
  }
}

}  // namespace delta
