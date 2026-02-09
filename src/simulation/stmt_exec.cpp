#include "simulation/stmt_exec.h"

#include <unordered_set>

#include "common/arena.h"
#include "elaboration/sensitivity.h"
#include "parser/ast.h"
#include "simulation/awaiters.h"
#include "simulation/eval.h"
#include "simulation/process.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"

namespace delta {

// --- Leaf executors (regular functions, no coroutine frame) ---

static StmtResult ExecBlockingAssignImpl(const Stmt* stmt, SimContext& ctx,
                                         Arena& arena) {
  auto rhs_val = EvalExpr(stmt->rhs, ctx, arena);
  if (stmt->lhs && stmt->lhs->kind == ExprKind::kIdentifier) {
    auto* var = ctx.FindVariable(stmt->lhs->text);
    if (var) {
      var->value = rhs_val;
      var->NotifyWatchers();
    }
  }
  return StmtResult::kDone;
}

static StmtResult ExecNonblockingAssignImpl(const Stmt* stmt, SimContext& ctx,
                                            Arena& arena) {
  auto rhs_val = EvalExpr(stmt->rhs, ctx, arena);
  if (!stmt->lhs || stmt->lhs->kind != ExprKind::kIdentifier) {
    return StmtResult::kDone;
  }
  auto* var = ctx.FindVariable(stmt->lhs->text);
  if (!var) return StmtResult::kDone;

  var->pending_nba = rhs_val;
  var->has_pending_nba = true;

  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  event->callback = [var]() {
    if (var->has_pending_nba) {
      var->value = var->pending_nba;
      var->has_pending_nba = false;
      var->NotifyWatchers();
    }
  };
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), Region::kNBA, event);
  return StmtResult::kDone;
}

static StmtResult ExecExprStmtImpl(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  EvalExpr(stmt->expr, ctx, arena);
  return StmtResult::kDone;
}

// --- Container coroutines (return ExecTask, support suspension) ---

static ExecTask ExecBlock(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  for (auto* s : stmt->stmts) {
    auto result = co_await ExecStmt(s, ctx, arena);
    if (result != StmtResult::kDone) co_return result;
    if (ctx.StopRequested()) co_return StmtResult::kDone;
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecIf(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  auto cond = EvalExpr(stmt->condition, ctx, arena);
  if (cond.ToUint64() != 0) {
    co_return co_await ExecStmt(stmt->then_branch, ctx, arena);
  }
  if (stmt->else_branch) {
    co_return co_await ExecStmt(stmt->else_branch, ctx, arena);
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecCase(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  auto sel = EvalExpr(stmt->condition, ctx, arena);
  uint64_t sel_val = sel.ToUint64();

  for (const auto& item : stmt->case_items) {
    if (item.is_default) continue;
    for (auto* pat : item.patterns) {
      auto pat_val = EvalExpr(pat, ctx, arena);
      if (pat_val.ToUint64() == sel_val) {
        co_return co_await ExecStmt(item.body, ctx, arena);
      }
    }
  }
  // Fall through to default.
  for (const auto& item : stmt->case_items) {
    if (item.is_default) co_return co_await ExecStmt(item.body, ctx, arena);
  }
  co_return StmtResult::kDone;
}

// --- Loops ---

static ExecTask ExecFor(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (stmt->for_init) co_await ExecStmt(stmt->for_init, ctx, arena);
  while (!ctx.StopRequested()) {
    if (stmt->for_cond) {
      auto cond = EvalExpr(stmt->for_cond, ctx, arena);
      if (cond.ToUint64() == 0) break;
    }
    auto result = co_await ExecStmt(stmt->for_body, ctx, arena);
    if (result == StmtResult::kBreak) break;
    if (result != StmtResult::kDone && result != StmtResult::kContinue) {
      co_return result;
    }
    if (stmt->for_step) co_await ExecStmt(stmt->for_step, ctx, arena);
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecWhile(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  while (!ctx.StopRequested()) {
    auto cond = EvalExpr(stmt->condition, ctx, arena);
    if (cond.ToUint64() == 0) break;
    auto result = co_await ExecStmt(stmt->body, ctx, arena);
    if (result == StmtResult::kBreak) break;
    if (result != StmtResult::kDone && result != StmtResult::kContinue) {
      co_return result;
    }
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecForever(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  while (!ctx.StopRequested()) {
    auto result = co_await ExecStmt(stmt->body, ctx, arena);
    if (result == StmtResult::kBreak) break;
    if (result != StmtResult::kDone && result != StmtResult::kContinue) {
      co_return result;
    }
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecRepeat(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  auto count_val = EvalExpr(stmt->condition, ctx, arena);
  auto count = count_val.ToUint64();
  for (uint64_t i = 0; i < count && !ctx.StopRequested(); ++i) {
    auto result = co_await ExecStmt(stmt->body, ctx, arena);
    if (result == StmtResult::kBreak) break;
    if (result != StmtResult::kDone && result != StmtResult::kContinue) {
      co_return result;
    }
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecDoWhile(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  do {
    auto result = co_await ExecStmt(stmt->body, ctx, arena);
    if (result == StmtResult::kBreak) break;
    if (result != StmtResult::kDone && result != StmtResult::kContinue) {
      co_return result;
    }
    auto cond = EvalExpr(stmt->condition, ctx, arena);
    if (cond.ToUint64() == 0) break;
  } while (!ctx.StopRequested());
  co_return StmtResult::kDone;
}

// --- Delay ---

static ExecTask ExecDelay(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  uint64_t ticks = 0;
  if (stmt->delay) {
    auto val = EvalExpr(stmt->delay, ctx, arena);
    ticks = val.ToUint64();
  }
  co_await DelayAwaiter{ctx, ticks};
  if (stmt->body) {
    co_return co_await ExecStmt(stmt->body, ctx, arena);
  }
  co_return StmtResult::kDone;
}

// --- Event control ---

static ExecTask ExecEventControl(const Stmt* stmt, SimContext& ctx,
                                 Arena& arena) {
  if (!stmt->events.empty()) {
    co_await EventAwaiter{ctx, stmt->events};
  }
  if (stmt->body) {
    co_return co_await ExecStmt(stmt->body, ctx, arena);
  }
  co_return StmtResult::kDone;
}

// --- Wait (IEEE §9.4.3) ---

static ExecTask ExecWait(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  std::unordered_set<std::string_view> reads;
  CollectExprReads(stmt->condition, reads);
  std::vector<std::string_view> read_vars(reads.begin(), reads.end());
  while (!ctx.StopRequested()) {
    auto cond = EvalExpr(stmt->condition, ctx, arena);
    if (cond.ToUint64() != 0) break;
    if (read_vars.empty()) co_return StmtResult::kDone;
    co_await AnyChangeAwaiter{ctx, read_vars};
  }
  if (stmt->body) {
    co_return co_await ExecStmt(stmt->body, ctx, arena);
  }
  co_return StmtResult::kDone;
}

// --- Fork/join (IEEE §9.3.2) ---

static SimCoroutine ForkChildCoroutine(const Stmt* body, SimContext& ctx,
                                       Arena& arena, ForkJoinState* state) {
  co_await ExecStmt(body, ctx, arena);
  state->remaining--;
  bool should_resume =
      state->join_any ? !state->resumed : (state->remaining == 0);
  if (should_resume && state->parent) {
    state->resumed = true;
    state->parent.resume();
  }
}

static void SpawnForkChildren(const Stmt* stmt, SimContext& ctx, Arena& arena,
                              ForkJoinState* state) {
  for (auto* s : stmt->fork_stmts) {
    auto* p = arena.Create<Process>();
    p->kind = ProcessKind::kInitial;
    p->coro = ForkChildCoroutine(s, ctx, arena, state).Release();
    auto* event = ctx.GetScheduler().GetEventPool().Acquire();
    event->callback = [p]() { p->Resume(); };
    ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), Region::kActive, event);
  }
}

static ExecTask ExecFork(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (stmt->fork_stmts.empty()) co_return StmtResult::kDone;

  auto* state = arena.Create<ForkJoinState>();
  state->remaining = static_cast<uint32_t>(stmt->fork_stmts.size());
  state->join_any = (stmt->join_kind == TokenKind::kKwJoinAny);

  SpawnForkChildren(stmt, ctx, arena, state);

  if (stmt->join_kind != TokenKind::kKwJoinNone) {
    co_await ForkJoinAwaiter{state};
  }
  co_return StmtResult::kDone;
}

// --- Main dispatch ---

ExecTask ExecStmt(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt) return ExecTask::Immediate(StmtResult::kDone);

  switch (stmt->kind) {
    case StmtKind::kNull:
      return ExecTask::Immediate(StmtResult::kDone);
    case StmtKind::kBlock:
      return ExecBlock(stmt, ctx, arena);
    case StmtKind::kIf:
      return ExecIf(stmt, ctx, arena);
    case StmtKind::kCase:
      return ExecCase(stmt, ctx, arena);
    case StmtKind::kFor:
      return ExecFor(stmt, ctx, arena);
    case StmtKind::kWhile:
      return ExecWhile(stmt, ctx, arena);
    case StmtKind::kForever:
      return ExecForever(stmt, ctx, arena);
    case StmtKind::kRepeat:
      return ExecRepeat(stmt, ctx, arena);
    case StmtKind::kDoWhile:
      return ExecDoWhile(stmt, ctx, arena);
    case StmtKind::kBlockingAssign:
      return ExecTask::Immediate(ExecBlockingAssignImpl(stmt, ctx, arena));
    case StmtKind::kNonblockingAssign:
      return ExecTask::Immediate(ExecNonblockingAssignImpl(stmt, ctx, arena));
    case StmtKind::kExprStmt:
      return ExecTask::Immediate(ExecExprStmtImpl(stmt, ctx, arena));
    case StmtKind::kDelay:
      return ExecDelay(stmt, ctx, arena);
    case StmtKind::kEventControl:
      return ExecEventControl(stmt, ctx, arena);
    case StmtKind::kFork:
      return ExecFork(stmt, ctx, arena);
    case StmtKind::kWait:
      return ExecWait(stmt, ctx, arena);
    case StmtKind::kTimingControl:
    case StmtKind::kDisable:
      return ExecTask::Immediate(StmtResult::kDone);
    case StmtKind::kBreak:
      return ExecTask::Immediate(StmtResult::kBreak);
    case StmtKind::kContinue:
      return ExecTask::Immediate(StmtResult::kContinue);
    case StmtKind::kReturn:
      return ExecTask::Immediate(StmtResult::kReturn);
    default:
      return ExecTask::Immediate(StmtResult::kDone);
  }
}

}  // namespace delta
