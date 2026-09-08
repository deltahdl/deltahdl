#include <coroutine>
#include <cstdint>
#include <iostream>
#include <memory>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "parser/ast.h"
#include "simulator/awaiters.h"
#include "simulator/evaluation.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_exec_internal.h"

namespace delta {
namespace {

// Rewrites any sequence name in the wait condition's read set to its synthetic
// endpoint event variable (creating that event variable on demand), so the wait
// suspends on the sequence's completion event rather than on the name itself.
void SubstituteSequenceEndpoints(std::unordered_set<std::string>& reads,
                                 SimContext& ctx) {
  std::unordered_set<std::string> seq_adds;
  std::unordered_set<std::string> seq_removes;
  for (const auto& name : reads) {
    if (ctx.FindSequenceDecl(name)) {
      std::string ep_name = "__seq_" + name;
      auto* ep_var = ctx.FindVariable(ep_name);
      if (!ep_var) {
        // variables_ keys by string_view, so intern the name in the arena;
        // a local std::string key would dangle once this function returns.
        auto* stored = ctx.GetArena().Create<std::string>(ep_name);
        ep_var = ctx.CreateVariable(*stored, 1);
        ep_var->is_event = true;
      }
      seq_adds.insert(ep_name);
      seq_removes.insert(name);
    }
  }
  for (const auto& r : seq_removes) reads.erase(r);
  for (auto& a : seq_adds) reads.insert(a);
}

struct WaitOrderStepAwaiter {
  SimContext& ctx;
  const std::vector<std::string_view>& event_names;
  std::string_view triggered_name;

  bool await_ready() const noexcept { return false; }

  void await_suspend(std::coroutine_handle<> h) {
    auto done = std::make_shared<bool>(false);
    auto* out = &triggered_name;

    for (auto name : event_names) {
      auto* var = ctx.FindVariable(name);
      if (!var) continue;
      var->AddWatcher([h, name, out, done]() mutable {
        if (*done) return true;
        *done = true;
        *out = name;
        h.resume();
        return true;
      });
    }
  }

  std::string_view await_resume() const noexcept { return triggered_name; }
};

// Collects the names of the wait_order events from index `start` onward, the
// set the next step must wait on while honoring the required ordering.
std::vector<std::string_view> RemainingWaitOrderNames(
    const std::vector<Expr*>& events, size_t start) {
  std::vector<std::string_view> remaining;
  for (size_t j = start; j < events.size(); ++j) {
    remaining.push_back(events[j]->text);
  }
  return remaining;
}

}  // namespace

ExecTask ExecWait(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  std::unordered_set<std::string> reads;
  CollectExprReads(stmt->condition, reads);

  SubstituteSequenceEndpoints(reads, ctx);
  std::vector<std::string_view> read_vars(reads.begin(), reads.end());
  // Shared with every watcher armed below: set true once the condition holds
  // and this coroutine resumes for good, so a watcher still stranded on a
  // sibling signal removes itself instead of resuming the (freed) frame.
  auto finished = std::make_shared<bool>(false);
  bool suspended = false;
  while (!ctx.StopRequested()) {
    auto cond = EvalExpr(stmt->condition, ctx, arena);
    if (cond.IsTruthy()) break;
    if (read_vars.empty()) {
      if (labeled) ctx.PopStaticScope(stmt->label);
      co_return StmtResult::kDone;
    }
    suspended = true;
    co_await AnyChangeAwaiter{ctx, read_vars, finished};
  }
  *finished = true;
  // §12.4.2.1: resuming after suspending on a wait statement is a violation
  // report flush point; drop any reports pending from before the wait.
  // §16.4.2: the same resume is a deferred assertion flush point.
  if (suspended) {
    ctx.FlushPendingViolations();
    ctx.FlushPendingDeferredReports();
  }
  if (stmt->body) {
    auto r = co_await ExecStmt(stmt->body, ctx, arena);
    if (labeled) ctx.PopStaticScope(stmt->label);
    co_return r;
  }
  if (labeled) ctx.PopStaticScope(stmt->label);
  co_return StmtResult::kDone;
}

ExecTask ExecWaitOrder(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  auto& events = stmt->wait_order_events;
  if (events.empty()) {
    if (stmt->then_branch) {
      co_return co_await ExecStmt(stmt->then_branch, ctx, arena);
    }
    co_return StmtResult::kDone;
  }

  bool failed = false;

  for (size_t i = 0; i < events.size() && !failed; ++i) {
    auto expected_name = events[i]->text;

    if (i == 0 && ctx.IsEventTriggered(expected_name)) {
      continue;
    }

    std::vector<std::string_view> remaining =
        RemainingWaitOrderNames(events, i);

    auto triggered = co_await WaitOrderStepAwaiter{ctx, remaining, {}};

    if (triggered != expected_name) {
      failed = true;
    }
  }

  if (failed) {
    if (stmt->else_branch) {
      co_return co_await ExecStmt(stmt->else_branch, ctx, arena);
    }

    // §15.5.4: when no else (fail) clause is supplied, a failed sequence
    // raises a default run-time error by calling $error (see §20.10), which
    // records ERROR severity and lets the run continue.
    EmitSeverityHeader(ctx, "ERROR", "wait_order events triggered out of order",
                       std::cerr);
    co_return StmtResult::kDone;
  }

  if (stmt->then_branch) {
    co_return co_await ExecStmt(stmt->then_branch, ctx, arena);
  }
  co_return StmtResult::kDone;
}

ExecTask ExecCycleDelay(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  uint32_t cycles = 0;
  if (stmt->cycle_delay) {
    auto val = EvalExpr(stmt->cycle_delay, ctx, arena);
    cycles = static_cast<uint32_t>(val.ToUint64());
  }
  if (cycles > 0) {
    co_await CycleDelayAwaiter{ctx, cycles};
  }
  if (stmt->body) {
    co_return co_await ExecStmt(stmt->body, ctx, arena);
  }
  co_return StmtResult::kDone;
}

uint64_t DelayTicksFromValue(const Logic4Vec& val) {
  if (!val.IsKnown()) return 0;
  uint64_t raw = val.ToUint64();
  if (val.is_signed && val.width > 0 && val.width < 64) {
    int64_t signed_val = SignExtend(raw, val.width);
    if (signed_val < 0) return static_cast<uint64_t>(signed_val);
  }
  return raw;
}

uint64_t DelayValueToTicks(const Logic4Vec& val, const SimContext& ctx) {
  const TimeScale& scale = ctx.CurrentTimeScale();
  TimeUnit precision = ctx.GlobalPrecision();
  if (val.is_real) {
    // §3.14.1: a real delay is rounded to the nearest multiple of the design
    // element's time precision before it is used. The value carries IEEE-754
    // bits in its low word; recover the number and let RealDelayToTicks apply
    // the precision-step rounding and scale the result to global-precision
    // ticks. A negative delay has no meaning here, so it collapses to no wait.
    double d = RealVecToDouble(val);
    if (d < 0.0) return 0;
    return RealDelayToTicks(d, scale, precision);
  }
  // An integer delay has no fractional part to round, but is still scaled from
  // the issuing element's time unit to the global tick base.
  return DelayToTicks(DelayTicksFromValue(val), scale, precision);
}

ExecTask ExecDelay(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  uint64_t ticks = 0;
  if (stmt->delay) {
    ticks = DelayValueToTicks(EvalExpr(stmt->delay, ctx, arena), ctx);
  }
  co_await DelayAwaiter{ctx, ticks};
  if (stmt->body) {
    co_return co_await ExecStmt(stmt->body, ctx, arena);
  }
  co_return StmtResult::kDone;
}

static bool IsNamedEvent(const Stmt* stmt, SimContext& ctx) {
  if (stmt->events.size() != 1) return false;
  const auto& ev = stmt->events[0];
  if (ev.edge != Edge::kNone) return false;
  // §9.4.2.3: a guarded operand goes to EventAwaiter, which evaluates the
  // condition before resuming. NamedEventAwaiter resumes on the trigger alone,
  // so sending `@(e iff en)` there would fire the process however `en` read.
  if (ev.iff_condition) return false;
  if (!ev.signal || ev.signal->kind != ExprKind::kIdentifier) return false;
  auto* var = ctx.FindVariable(ev.signal->text);
  return var && var->is_event;
}

static bool HasSequenceEvent(const Stmt* stmt) {
  for (const auto& ev : stmt->events) {
    if (ev.is_sequence_event) return true;
  }
  return false;
}

ExecTask ExecEventControl(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt->events.empty()) {
    if (HasSequenceEvent(stmt)) {
      co_await SequenceEventAwaiter{ctx, stmt->events};
    } else if (IsNamedEvent(stmt, ctx)) {
      co_await NamedEventAwaiter{ctx, stmt->events[0].signal->text};
    } else {
      co_await EventAwaiter{ctx, stmt->events, arena};
    }
    // §12.4.2.1: a process that suspended on an event control reaches a
    // violation report flush point when it resumes; any unique/priority
    // reports accumulated before the suspension are discarded.
    ctx.FlushPendingViolations();
    // §16.4.2: that resume is equally a deferred assertion flush point, so
    // deferred reports pending from before the suspend are cleared as well.
    ctx.FlushPendingDeferredReports();
  } else if (stmt->is_star_event && stmt->body) {
    // §9.4.2.2: a procedural @* (or @(*)) carries no explicit operand list; it
    // suspends until any net or variable read by its controlled statement
    // changes. Derive that implicit event list from the statement's reads --
    // the same read-collection rule the elaborator applies to `always @*` --
    // and wait on it as though it had been written out as @(a or b or ...).
    // The vector must outlive the suspension, so it lives in this coroutine
    // frame. `exclude_written` is false because @* (unlike always_comb) still
    // lists a signal that is both read and written.
    std::vector<EventExpr> implicit_events = InferSensitivity(
        stmt->body, arena, /*funcs=*/nullptr, /*exclude_written=*/false);
    if (!implicit_events.empty()) {
      co_await EventAwaiter{ctx, implicit_events, arena};
      ctx.FlushPendingViolations();
      ctx.FlushPendingDeferredReports();
    }
  }
  if (stmt->body) {
    co_return co_await ExecStmt(stmt->body, ctx, arena);
  }
  co_return StmtResult::kDone;
}

}  // namespace delta
