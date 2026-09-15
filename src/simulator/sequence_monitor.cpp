#include "simulator/sequence_monitor.h"

#include <cstddef>
#include <cstdint>
#include <string>
#include <utility>
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

// One attempt of the sequence part way through: the operand it is to match
// next and the clock ticks that have passed since the operand before it
// matched, or since the attempt began for the first operand.
struct LinearAttempt {
  size_t pos;
  uint32_t waited;
};

// §16.7: the delay before an operand is a range of clock ticks, and the
// operand is checked at every tick within it, so an attempt inside the range
// matches at each such tick the operand holds at and stays alive to the range's
// end. A delay with no upper bound keeps the attempt alive for the run, and
// once its wait has reached the lower bound every further tick reads the same,
// so its wait is held at that bound and the attempts that reach it coincide.
static bool WithinDelay(const SeqCycleDelay& delay, uint32_t waited) {
  return waited >= delay.min && waited <= delay.max;
}

static void CarryAttempt(LinearAttempt attempt, const SeqCycleDelay& delay,
                         std::vector<LinearAttempt>& carry) {
  if (attempt.waited >= delay.max) return;
  if (delay.max == SeqCycleDelay::kUnbounded && attempt.waited > delay.min) {
    attempt.waited = delay.min;
  }
  for (const auto& kept : carry) {
    if (kept.pos == attempt.pos && kept.waited == attempt.waited) return;
  }
  carry.push_back(attempt);
}

// §16.14.5 always-semantics: one clock tick of every in-flight attempt, and of
// the fresh attempt this tick begins. An attempt whose operand's delay the
// tick falls within checks the operand: holding, it matches the sequence at
// its last operand or begins waiting for the next, a next operand with a `##0`
// before it checked at this same tick as §16.7 has the concatenation with a
// delay of 0 overlap; and whether or not it holds, the attempt stays for the
// later ticks of its range. Reports whether any attempt matched at this tick.
bool AdvanceLinearAttempts(const std::vector<Expr*>& operands,
                           const std::vector<SeqCycleDelay>& delays,
                           std::vector<LinearAttempt>& active, SimContext& ctx,
                           Arena& arena) {
  std::vector<LinearAttempt> pending;
  pending.reserve(active.size() + 1);
  for (LinearAttempt attempt : active) {
    ++attempt.waited;
    pending.push_back(attempt);
  }
  pending.push_back({0, 0});
  std::vector<LinearAttempt> carry;
  bool matched = false;
  while (!pending.empty()) {
    LinearAttempt attempt = pending.back();
    pending.pop_back();
    const SeqCycleDelay& delay = delays[attempt.pos];
    if (WithinDelay(delay, attempt.waited) &&
        EvalExpr(operands[attempt.pos], ctx, arena).IsTruthy()) {
      if (attempt.pos + 1 == operands.size()) {
        matched = true;
      } else {
        pending.push_back({attempt.pos + 1, 0});
      }
    }
    CarryAttempt(attempt, delay, carry);
  }
  active = std::move(carry);
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

SimCoroutine MakeSequenceMonitorCoroutine(LinearSequence body,
                                          std::vector<EventExpr> clock,
                                          std::string ep_name, SimContext& ctx,
                                          Arena& arena) {
  std::vector<LinearAttempt> active;
  while (!ctx.StopRequested()) {
    co_await EventAwaiter{ctx, clock, arena};
    // §16.14.5: a new evaluation attempt begins at every clock tick, which
    // AdvanceLinearAttempts adds beside the ones in flight.
    if (AdvanceLinearAttempts(body.operands, body.delays, active, ctx, arena)) {
      FireSequenceEndpoint(ctx, ep_name);
    }
  }
}

}  // namespace delta
