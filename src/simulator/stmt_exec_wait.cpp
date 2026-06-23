#include <iostream>
#include <memory>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
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
        ep_var = ctx.CreateVariable(ep_name, 1);
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
  // Shared with every watcher armed below: set true once the condition is met
  // and this coroutine resumes for good, so any watcher still stranded on a
  // sibling signal removes itself instead of resuming the (by then freed) frame.
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
  if (suspended) ctx.FlushPendingViolations();
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

}  // namespace delta
