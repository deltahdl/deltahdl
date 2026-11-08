#include "elaborator/elaborator_process_validate.h"

#include <format>
#include <string>
#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

bool StmtHasForkJoin(const Stmt* stmt) {
  if (!stmt) return false;
  if (stmt->kind == StmtKind::kFork) return true;
  bool found = false;
  ForEachChildStmt(stmt, [&](Stmt* const& sub) {
    if (found) return;
    found = StmtHasForkJoin(sub);
  });
  return found;
}

using AssignedNames = std::unordered_set<std::string_view>;

std::string_view AssignedVariable(const Expr* lhs) {
  const Expr* e = lhs;
  while (e) {
    if (e->kind == ExprKind::kIdentifier) return e->text;
    if (e->kind == ExprKind::kSelect) {
      e = e->base;
      continue;
    }
    if (e->kind == ExprKind::kMemberAccess) {
      e = e->lhs;
      continue;
    }
    break;
  }
  return {};
}

void CollectAssignedVariables(const Stmt* stmt, AssignedNames& out) {
  if (!stmt) return;
  if (stmt->kind == StmtKind::kBlockingAssign ||
      stmt->kind == StmtKind::kNonblockingAssign) {
    auto name = AssignedVariable(stmt->lhs);
    if (!name.empty()) out.insert(name);
  }
  ForEachChildStmt(
      stmt, [&](Stmt* const& sub) { CollectAssignedVariables(sub, out); });
}

void KeepOnlyCommon(AssignedNames& acc, const AssignedNames& other) {
  for (auto it = acc.begin(); it != acc.end();) {
    if (other.find(*it) == other.end()) {
      it = acc.erase(it);
    } else {
      ++it;
    }
  }
}

void KeepBoth(AssignedNames& acc, const AssignedNames& other) {
  acc.insert(other.begin(), other.end());
}

AssignedNames AssignedOnEveryPath(const Stmt* stmt);

AssignedNames AssignedOnEveryForkPath(const Stmt* stmt) {
  AssignedNames out;
  if (stmt->join_kind != TokenKind::kKwJoin) return out;
  for (const auto* s : stmt->fork_stmts) KeepBoth(out, AssignedOnEveryPath(s));
  return out;
}

AssignedNames AssignedOnEveryForPath(const Stmt* stmt) {
  AssignedNames out;
  for (const auto* s : stmt->for_inits) KeepBoth(out, AssignedOnEveryPath(s));
  KeepBoth(out, AssignedOnEveryPath(stmt->for_body));
  for (const auto* s : stmt->for_steps) KeepBoth(out, AssignedOnEveryPath(s));
  return out;
}

AssignedNames AssignedOnEveryCasePath(const Stmt* stmt) {
  AssignedNames common;
  bool has_default = false;
  for (const auto& ci : stmt->case_items)
    if (ci.is_default) has_default = true;
  if (!has_default) return common;
  bool started = false;
  for (const auto& ci : stmt->case_items) {
    AssignedNames item = AssignedOnEveryPath(ci.body);
    if (started) {
      KeepOnlyCommon(common, item);
      continue;
    }
    common = item;
    started = true;
  }
  return common;
}

AssignedNames AssignedOnEveryPath(const Stmt* stmt) {
  AssignedNames out;
  if (!stmt) return out;
  switch (stmt->kind) {
    case StmtKind::kBlockingAssign:
    case StmtKind::kNonblockingAssign: {
      auto name = AssignedVariable(stmt->lhs);
      if (!name.empty()) out.insert(name);
      return out;
    }
    case StmtKind::kBlock:
      for (const auto* s : stmt->stmts) KeepBoth(out, AssignedOnEveryPath(s));
      return out;
    case StmtKind::kIf:
      if (!stmt->else_branch) return out;
      out = AssignedOnEveryPath(stmt->then_branch);
      KeepOnlyCommon(out, AssignedOnEveryPath(stmt->else_branch));
      return out;
    case StmtKind::kCase:
      return AssignedOnEveryCasePath(stmt);
    case StmtKind::kFork:
      return AssignedOnEveryForkPath(stmt);
    case StmtKind::kFor:
      return AssignedOnEveryForPath(stmt);
    case StmtKind::kForeach:
    case StmtKind::kWhile:
    case StmtKind::kDoWhile:
    case StmtKind::kForever:
    case StmtKind::kRepeat:
      return AssignedOnEveryPath(stmt->body);
    default:
      return out;
  }
}

bool InfersLatch(const Stmt* body) {
  AssignedNames assigned;
  CollectAssignedVariables(body, assigned);
  AssignedNames every_path = AssignedOnEveryPath(body);
  for (auto name : assigned)
    if (every_path.find(name) == every_path.end()) return true;
  return false;
}

bool StmtBlocks(const Stmt* stmt, bool include_nonblocking_intra = false);

bool StmtBlocks(const Stmt* stmt, bool include_nonblocking_intra) {
  if (!stmt) return false;
  switch (stmt->kind) {
    case StmtKind::kTimingControl:
    case StmtKind::kDelay:
    case StmtKind::kCycleDelay:
    case StmtKind::kEventControl:
    case StmtKind::kWait:
    case StmtKind::kWaitOrder:
    case StmtKind::kWaitFork:
    case StmtKind::kExpect:
      return true;
    case StmtKind::kBlockingAssign:
    case StmtKind::kNonblockingAssign:
      return (stmt->kind == StmtKind::kBlockingAssign ||
              include_nonblocking_intra) &&
             (stmt->delay != nullptr || stmt->cycle_delay != nullptr ||
              !stmt->events.empty());
    default:
      break;
  }
  bool found = false;
  ForEachChildStmt(stmt, [&](Stmt* const& sub) {
    if (found) return;
    found = StmtBlocks(sub, include_nonblocking_intra);
  });
  return found;
}

bool StmtEnablesTask(const Stmt* stmt,
                     const std::unordered_set<std::string>& task_names) {
  if (!stmt) return false;
  if (task_names.contains(EnabledSubroutineName(stmt))) return true;
  bool found = false;
  ForEachChildStmt(stmt, [&](Stmt* const& sub) {
    if (found) return;
    found = StmtEnablesTask(sub, task_names);
  });
  return found;
}

void ValidateCombLatchProcess(ModuleItem* item, const RtlirProcess& proc,
                              RtlirProcessKind kind, DiagEngine& diag) {
  if (kind != RtlirProcessKind::kAlwaysComb &&
      kind != RtlirProcessKind::kAlwaysLatch)
    return;
  const bool kIsComb = kind == RtlirProcessKind::kAlwaysComb;
  const char* kw = kIsComb ? "always_comb" : "always_latch";
  const Subclause kRule =
      kIsComb ? Subclause("9.2.2.2.2") : Subclause("9.2.2.3");
  if (!item->sensitivity.empty() || item->is_star_sensitivity) {
    diag.Error(item->loc,
               std::format("{} shall not have an explicit event control", kw),
               kRule);
  }
  if (StmtBlocks(proc.body)) {
    diag.Error(item->loc,
               std::format("{} shall not contain timing controls", kw), kRule);
  }
  if (StmtHasForkJoin(proc.body)) {
    diag.Error(item->loc,
               std::format("{} shall not contain fork-join statements", kw),
               kRule);
  }
  if (kIsComb && InfersLatch(proc.body)) {
    diag.Warning(item->loc,
                 "always_comb may infer latched behavior; "
                 "ensure all paths assign all outputs",
                 Subclause("9.2.2.2"));
  }
  if (!kIsComb && !InfersLatch(proc.body)) {
    diag.Warning(item->loc,
                 "always_latch does not infer latched behavior; "
                 "ensure incomplete assignments create intended latches",
                 Subclause("9.2.2.3"));
  }
}

void ValidateAlwaysFFProcess(ModuleItem* item, const RtlirProcess& proc,
                             DiagEngine& diag) {
  if (proc.sensitivity.empty()) {
    diag.Error(item->loc, "always_ff requires an event control",
               Subclause("9.2.2.4"));
  }
  if (StmtBlocks(proc.body)) {
    diag.Error(item->loc,
               "always_ff shall not contain blocking timing controls",
               Subclause("9.2.2.4"));
  }
  if (StmtHasForkJoin(proc.body)) {
    diag.Error(item->loc, "always_ff shall not contain fork-join statements",
               Subclause("9.2.2.4"));
  }
  bool has_edge = false;
  for (const auto& ev : proc.sensitivity) {
    if (ev.edge == Edge::kPosedge || ev.edge == Edge::kNegedge) {
      has_edge = true;
      break;
    }
  }
  bool concurrent = proc.body != nullptr && proc.body->is_concurrent_clocked;
  if (!proc.sensitivity.empty() && !has_edge && !concurrent) {
    diag.Warning(item->loc,
                 "always_ff has no edge-sensitive event; "
                 "may not represent sequential logic",
                 Subclause("9.2.2.4"));
  }
}

void ValidateFinalProcess(ModuleItem* item, const RtlirProcess& proc,
                          DiagEngine& diag) {
  if (StmtBlocks(proc.body, true)) {
    diag.Error(item->loc, "final procedure shall not contain timing controls",
               Subclause("9.2.3"));
  }
  if (StmtHasForkJoin(proc.body)) {
    diag.Error(item->loc,
               "final procedure shall not contain fork-join statements",
               Subclause("9.2.3"));
  }
}

}  // namespace

void ValidateProcess(RtlirProcessKind kind, ModuleItem* item,
                     const RtlirProcess& proc, DiagEngine& diag,
                     const std::unordered_set<std::string>& task_names) {
  if (kind == RtlirProcessKind::kAlways && item->sensitivity.empty() &&
      !item->is_star_sensitivity && !StmtBlocks(proc.body) &&
      !StmtEnablesTask(proc.body, task_names)) {
    diag.Warning(item->loc,
                 "always block has no timing control; may cause "
                 "a zero-delay loop",
                 Subclause("9.2.2.1"));
  }
  ValidateCombLatchProcess(item, proc, kind, diag);
  if (kind == RtlirProcessKind::kAlwaysFF) {
    ValidateAlwaysFFProcess(item, proc, diag);
  }
  if (kind == RtlirProcessKind::kFinal) {
    ValidateFinalProcess(item, proc, diag);
  }
}

}  // namespace delta
