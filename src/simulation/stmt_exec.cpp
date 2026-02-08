#include "simulation/stmt_exec.h"

#include "common/arena.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

namespace delta {

// Forward declaration for mutual recursion.
StmtResult ExecStmt(const Stmt* stmt, SimContext& ctx, Arena& arena);

// --- Block ---

static StmtResult ExecBlock(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  for (auto* s : stmt->stmts) {
    auto result = ExecStmt(s, ctx, arena);
    if (result != StmtResult::kDone) return result;
    if (ctx.StopRequested()) return StmtResult::kDone;
  }
  return StmtResult::kDone;
}

// --- If ---

static StmtResult ExecIf(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  auto cond = EvalExpr(stmt->condition, ctx, arena);
  if (cond.ToUint64() != 0) {
    return ExecStmt(stmt->then_branch, ctx, arena);
  }
  if (stmt->else_branch) {
    return ExecStmt(stmt->else_branch, ctx, arena);
  }
  return StmtResult::kDone;
}

// --- Case ---

static StmtResult ExecCaseItem(const CaseItem& item, SimContext& ctx,
                               Arena& arena) {
  if (item.body) return ExecStmt(item.body, ctx, arena);
  return StmtResult::kDone;
}

static StmtResult ExecCase(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  auto sel = EvalExpr(stmt->condition, ctx, arena);
  uint64_t sel_val = sel.ToUint64();

  for (const auto& item : stmt->case_items) {
    if (item.is_default) continue;
    for (auto* pat : item.patterns) {
      auto pat_val = EvalExpr(pat, ctx, arena);
      if (pat_val.ToUint64() == sel_val) {
        return ExecCaseItem(item, ctx, arena);
      }
    }
  }
  // Fall through to default.
  for (const auto& item : stmt->case_items) {
    if (item.is_default) return ExecCaseItem(item, ctx, arena);
  }
  return StmtResult::kDone;
}

// --- Loops ---

static StmtResult ExecFor(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (stmt->for_init) ExecStmt(stmt->for_init, ctx, arena);
  while (!ctx.StopRequested()) {
    if (stmt->for_cond) {
      auto cond = EvalExpr(stmt->for_cond, ctx, arena);
      if (cond.ToUint64() == 0) break;
    }
    auto result = ExecStmt(stmt->for_body, ctx, arena);
    if (result == StmtResult::kBreak) break;
    if (result != StmtResult::kDone && result != StmtResult::kContinue) {
      return result;
    }
    if (stmt->for_step) ExecStmt(stmt->for_step, ctx, arena);
  }
  return StmtResult::kDone;
}

static StmtResult ExecWhile(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  while (!ctx.StopRequested()) {
    auto cond = EvalExpr(stmt->condition, ctx, arena);
    if (cond.ToUint64() == 0) break;
    auto result = ExecStmt(stmt->body, ctx, arena);
    if (result == StmtResult::kBreak) break;
    if (result != StmtResult::kDone && result != StmtResult::kContinue) {
      return result;
    }
  }
  return StmtResult::kDone;
}

static StmtResult ExecForever(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  while (!ctx.StopRequested()) {
    auto result = ExecStmt(stmt->body, ctx, arena);
    if (result == StmtResult::kBreak) break;
    if (result != StmtResult::kDone && result != StmtResult::kContinue) {
      return result;
    }
  }
  return StmtResult::kDone;
}

static StmtResult ExecRepeat(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  auto count_val = EvalExpr(stmt->condition, ctx, arena);
  auto count = count_val.ToUint64();
  for (uint64_t i = 0; i < count && !ctx.StopRequested(); ++i) {
    auto result = ExecStmt(stmt->body, ctx, arena);
    if (result == StmtResult::kBreak) break;
    if (result != StmtResult::kDone && result != StmtResult::kContinue) {
      return result;
    }
  }
  return StmtResult::kDone;
}

// --- Do-while ---

static StmtResult ExecDoWhile(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  do {
    auto result = ExecStmt(stmt->body, ctx, arena);
    if (result == StmtResult::kBreak) break;
    if (result != StmtResult::kDone && result != StmtResult::kContinue) {
      return result;
    }
    auto cond = EvalExpr(stmt->condition, ctx, arena);
    if (cond.ToUint64() == 0) break;
  } while (!ctx.StopRequested());
  return StmtResult::kDone;
}

// --- Assignments ---

static StmtResult ExecBlockingAssign(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena) {
  auto rhs_val = EvalExpr(stmt->rhs, ctx, arena);
  if (stmt->lhs && stmt->lhs->kind == ExprKind::kIdentifier) {
    auto* var = ctx.FindVariable(stmt->lhs->text);
    if (var) var->value = rhs_val;
  }
  return StmtResult::kDone;
}

// --- Expression statement ---

static StmtResult ExecExprStmt(const Stmt* stmt, SimContext& ctx,
                               Arena& arena) {
  EvalExpr(stmt->expr, ctx, arena);
  return StmtResult::kDone;
}

// --- Main dispatch ---

StmtResult ExecStmt(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt) return StmtResult::kDone;

  switch (stmt->kind) {
    case StmtKind::kNull:
      return StmtResult::kDone;
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
    case StmtKind::kBlockingAssign:
    case StmtKind::kNonblockingAssign:
      return ExecBlockingAssign(stmt, ctx, arena);
    case StmtKind::kExprStmt:
      return ExecExprStmt(stmt, ctx, arena);
    case StmtKind::kDelay:
      return StmtResult::kSuspendDelay;
    case StmtKind::kEventControl:
      return StmtResult::kSuspendEvent;
    case StmtKind::kFork:
      // Stub: execute each fork statement sequentially.
      for (auto* s : stmt->fork_stmts) {
        ExecStmt(s, ctx, arena);
      }
      return StmtResult::kDone;
    case StmtKind::kDoWhile:
      return ExecDoWhile(stmt, ctx, arena);
    case StmtKind::kTimingControl:
    case StmtKind::kWait:
    case StmtKind::kDisable:
      return StmtResult::kDone;
    case StmtKind::kBreak:
      return StmtResult::kBreak;
    case StmtKind::kContinue:
      return StmtResult::kContinue;
    case StmtKind::kReturn:
      return StmtResult::kReturn;
    default:
      return StmtResult::kDone;
  }
}

}  // namespace delta
