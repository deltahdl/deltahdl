#include <algorithm>
#include <format>
#include <functional>
#include <unordered_map>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

// Mark a single event-control event that names a known sequence, and flag the
// automatic-variable argument restriction (`s` supplies the location).
static void MarkSequenceEvent(
    Stmt* s, EventExpr& ev,
    const std::unordered_set<std::string_view>& seq_names, bool in_automatic,
    DiagEngine& diag) {
  if (!ev.signal) return;
  std::string_view name;
  bool has_args = false;
  if (ev.signal->kind == ExprKind::kIdentifier) {
    name = ev.signal->text;
  } else if (ev.signal->kind == ExprKind::kCall) {
    name = ev.signal->callee;
    has_args = !ev.signal->args.empty();
  }
  if (!name.empty() && seq_names.count(name) != 0) {
    ev.is_sequence_event = true;

    if (has_args && in_automatic) {
      diag.Error(s->range.start,
                 "sequence event arguments shall not reference "
                 "automatic variables");
    }
  }
}

static void WalkStmtsForSequenceEvents(
    Stmt* s, const std::unordered_set<std::string_view>& seq_names,
    bool in_automatic, DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kEventControl) {
    for (auto& ev : s->events) {
      MarkSequenceEvent(s, ev, seq_names, in_automatic, diag);
    }
  }
  for (auto* sub : s->stmts)
    WalkStmtsForSequenceEvents(sub, seq_names, in_automatic, diag);
  WalkStmtsForSequenceEvents(s->then_branch, seq_names, in_automatic, diag);
  WalkStmtsForSequenceEvents(s->else_branch, seq_names, in_automatic, diag);
  WalkStmtsForSequenceEvents(s->body, seq_names, in_automatic, diag);
  WalkStmtsForSequenceEvents(s->for_body, seq_names, in_automatic, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForSequenceEvents(ci.body, seq_names, in_automatic, diag);
}

void Elaborator::ValidateSequenceEventArgs(const ModuleDecl* decl) {
  if (sequence_names_.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kInitialBlock ||
        item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock ||
        item->kind == ModuleItemKind::kFinalBlock) {
      if (item->body) {
        WalkStmtsForSequenceEvents(const_cast<Stmt*>(item->body),
                                   sequence_names_, false, diag_);
      }
    }

    if (item->kind == ModuleItemKind::kTaskDecl) {
      // A task body's statements live in func_body_stmts (item->body is the
      // module-process body form); walk them so an event control such as
      // @(s(a, b)) inside an automatic task is reached. §9.4.2.4: arguments to
      // a sequence used in an event control shall be static, so an automatic
      // task local passed as a sequence argument is an error.
      if (item->body) {
        WalkStmtsForSequenceEvents(const_cast<Stmt*>(item->body),
                                   sequence_names_, item->is_automatic, diag_);
      }
      for (auto* s : item->func_body_stmts) {
        WalkStmtsForSequenceEvents(s, sequence_names_, item->is_automatic,
                                   diag_);
      }
    }
  }
}

static bool IsSingleSubroutineCall(const Stmt* action) {
  if (!action) return true;
  if (action->kind == StmtKind::kNull) return true;
  if (action->kind != StmtKind::kExprStmt) return false;
  if (!action->expr) return false;
  return action->expr->kind == ExprKind::kCall ||
         action->expr->kind == ExprKind::kSystemCall;
}

static bool ContainsPostponedIllegalStmt(const Stmt* s) {
  if (!s) return false;
  switch (s->kind) {
    case StmtKind::kBlockingAssign:
    case StmtKind::kNonblockingAssign:
    case StmtKind::kAssign:
    case StmtKind::kDeassign:
    case StmtKind::kForce:
    case StmtKind::kRelease:
    case StmtKind::kEventTrigger:
    case StmtKind::kNbEventTrigger:
    case StmtKind::kDelay:
    case StmtKind::kEventControl:
    case StmtKind::kWait:
    case StmtKind::kCycleDelay:
      return true;
    default:
      break;
  }
  for (auto* sub : s->stmts) {
    if (ContainsPostponedIllegalStmt(sub)) return true;
  }
  if (ContainsPostponedIllegalStmt(s->then_branch)) return true;
  if (ContainsPostponedIllegalStmt(s->else_branch)) return true;
  if (ContainsPostponedIllegalStmt(s->body)) return true;
  if (ContainsPostponedIllegalStmt(s->for_body)) return true;
  for (const auto& ci : s->case_items) {
    if (ContainsPostponedIllegalStmt(ci.body)) return true;
  }
  return false;
}

static bool CalleeBodyHasPostponedIllegal(const ModuleItem* callee) {
  if (!callee) return false;
  if (callee->body && ContainsPostponedIllegalStmt(callee->body)) return true;
  for (auto* s : callee->func_body_stmts) {
    if (ContainsPostponedIllegalStmt(s)) return true;
  }
  return false;
}

using DeferredSubroutineMap =
    std::unordered_map<std::string_view, const ModuleItem*>;

static void CheckFinalDeferredCallee(const Stmt* action,
                                     const DeferredSubroutineMap& subs,
                                     DiagEngine& diag) {
  if (!IsSingleSubroutineCall(action)) return;
  if (!action || action->kind != StmtKind::kExprStmt || !action->expr) return;
  if (action->expr->kind != ExprKind::kCall) return;
  auto it = subs.find(action->expr->callee);
  if (it == subs.end()) return;
  if (CalleeBodyHasPostponedIllegal(it->second)) {
    diag.Warning(
        action->range.start,
        std::format("§16.4: final deferred assertion calls '{}', whose body "
                    "contains statements not legally callable in the "
                    "Postponed region (§4.4.2.9)",
                    action->expr->callee));
  }
}

static void CheckDeferredCallRefArgs(const Stmt* action,
                                     const DeferredSubroutineMap& subs,
                                     DiagEngine& diag) {
  if (!IsSingleSubroutineCall(action)) return;
  if (!action || action->kind != StmtKind::kExprStmt || !action->expr) return;
  if (action->expr->kind != ExprKind::kCall) return;
  auto it = subs.find(action->expr->callee);
  if (it == subs.end()) return;
  const auto& formals = it->second->func_args;
  const auto& actuals = action->expr->args;
  size_t n = std::min(formals.size(), actuals.size());
  for (size_t i = 0; i < n; ++i) {
    if (formals[i].direction != Direction::kRef) continue;
    const Expr* a = actuals[i];
    if (!a) continue;
    if (a->kind == ExprKind::kMemberAccess) {
      diag.Error(
          a->range.start,
          std::format("§16.4: cannot pass dynamic variable as actual for "
                      "ref{} formal '{}' in deferred-assertion call",
                      formals[i].is_const ? " const" : "", formals[i].name));
    }
  }
}

static void CheckDeferredActionStmt(const Stmt* s,
                                    const DeferredSubroutineMap& subs,
                                    DiagEngine& diag) {
  if (!s->is_deferred) return;
  if (s->kind != StmtKind::kAssertImmediate &&
      s->kind != StmtKind::kAssumeImmediate &&
      s->kind != StmtKind::kCoverImmediate) {
    return;
  }
  if (s->assert_pass_stmt && !IsSingleSubroutineCall(s->assert_pass_stmt)) {
    diag.Warning(s->assert_pass_stmt->range.start,
                 "§16.4: deferred assertion pass action shall be a single "
                 "subroutine call");
  }
  if (s->assert_fail_stmt && !IsSingleSubroutineCall(s->assert_fail_stmt)) {
    diag.Warning(s->assert_fail_stmt->range.start,
                 "§16.4: deferred assertion fail action shall be a single "
                 "subroutine call");
  }

  if (s->is_final_deferred) {
    CheckFinalDeferredCallee(s->assert_pass_stmt, subs, diag);
    CheckFinalDeferredCallee(s->assert_fail_stmt, subs, diag);
  }

  CheckDeferredCallRefArgs(s->assert_pass_stmt, subs, diag);
  CheckDeferredCallRefArgs(s->assert_fail_stmt, subs, diag);
}

void Elaborator::WalkStmtsForDeferredActions(const Stmt* s) {
  if (!s) return;
  CheckDeferredActionStmt(s, deferred_subroutine_map_, diag_);
  for (auto* sub : s->stmts) WalkStmtsForDeferredActions(sub);
  WalkStmtsForDeferredActions(s->then_branch);
  WalkStmtsForDeferredActions(s->else_branch);
  WalkStmtsForDeferredActions(s->body);
  WalkStmtsForDeferredActions(s->for_body);
  WalkStmtsForDeferredActions(s->assert_pass_stmt);
  WalkStmtsForDeferredActions(s->assert_fail_stmt);
  for (const auto& ci : s->case_items) WalkStmtsForDeferredActions(ci.body);
}

void Elaborator::ValidateDeferredAssertionActions(const ModuleDecl* decl) {
  deferred_subroutine_map_.clear();
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kTaskDecl ||
        item->kind == ModuleItemKind::kFunctionDecl) {
      deferred_subroutine_map_[item->name] = item;
    }
  }
  for (const auto* item : decl->items) {
    if (item->body) {
      WalkStmtsForDeferredActions(item->body);
    }
  }
}

}  // namespace delta
