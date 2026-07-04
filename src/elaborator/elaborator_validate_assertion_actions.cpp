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

using SequenceDeclMap = std::unordered_map<std::string_view, const ModuleItem*>;

// §16.8: an instance of a named sequence shall provide an actual argument for
// each formal argument that does not have a default actual argument declared.
// This checks the positional-binding form of an instance used in an event
// control; named or partially-omitted binding is left to the general
// argument-binding machinery.
static void CheckSequenceActualArgCount(Stmt* s, const Expr* call,
                                        const ModuleItem* decl,
                                        DiagEngine& diag) {
  // Only the purely-positional, fully-supplied form is validated here: a named
  // binding populates arg_names, and an omitted actual leaves a null arg.
  if (!call->arg_names.empty()) return;
  for (const auto* a : call->args) {
    if (!a) return;
  }
  size_t actuals = call->args.size();
  size_t total = decl->prop_formals.size();
  size_t required = 0;
  for (size_t i = 0; i < total; ++i) {
    bool has_default = i < decl->prop_formal_has_default.size() &&
                       decl->prop_formal_has_default[i];
    if (!has_default) ++required;
  }
  if (actuals < required) {
    diag.Error(s->range.start,
               "sequence instance omits an actual argument for a formal that "
               "has no default (§16.8)");
  } else if (actuals > total) {
    diag.Error(s->range.start,
               "sequence instance provides more actual arguments than the "
               "sequence has formal arguments (§16.8)");
  }
}

// Mark a single event-control event that names a known sequence, flag the
// §9.4.2.4 automatic-variable argument restriction, and enforce the §16.8
// actual-argument count rule (`s` supplies the location).
static void MarkSequenceEvent(
    Stmt* s, EventExpr& ev,
    const std::unordered_set<std::string_view>& seq_names,
    const SequenceDeclMap& seq_decls, bool in_automatic, DiagEngine& diag) {
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
    if (ev.signal->kind == ExprKind::kCall) {
      auto it = seq_decls.find(name);
      if (it != seq_decls.end()) {
        CheckSequenceActualArgCount(s, ev.signal, it->second, diag);
      }
    }
  }
}

static void WalkStmtsForSequenceEvents(
    Stmt* s, const std::unordered_set<std::string_view>& seq_names,
    const SequenceDeclMap& seq_decls, bool in_automatic, DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kEventControl) {
    for (auto& ev : s->events) {
      MarkSequenceEvent(s, ev, seq_names, seq_decls, in_automatic, diag);
    }
  }
  for (auto* sub : s->stmts)
    WalkStmtsForSequenceEvents(sub, seq_names, seq_decls, in_automatic, diag);
  WalkStmtsForSequenceEvents(s->then_branch, seq_names, seq_decls, in_automatic,
                             diag);
  WalkStmtsForSequenceEvents(s->else_branch, seq_names, seq_decls, in_automatic,
                             diag);
  WalkStmtsForSequenceEvents(s->body, seq_names, seq_decls, in_automatic, diag);
  WalkStmtsForSequenceEvents(s->for_body, seq_names, seq_decls, in_automatic,
                             diag);
  for (auto& ci : s->case_items)
    WalkStmtsForSequenceEvents(ci.body, seq_names, seq_decls, in_automatic,
                               diag);
}

static bool IsProcessBlockItem(ModuleItemKind kind) {
  switch (kind) {
    case ModuleItemKind::kInitialBlock:
    case ModuleItemKind::kAlwaysBlock:
    case ModuleItemKind::kAlwaysCombBlock:
    case ModuleItemKind::kAlwaysFFBlock:
    case ModuleItemKind::kAlwaysLatchBlock:
    case ModuleItemKind::kFinalBlock:
      return true;
    default:
      return false;
  }
}

// Walk one module item's statements for sequence-event arguments. A process
// block's statements live in item->body; a task body's statements live in
// func_body_stmts (item->body is the module-process body form), so both are
// walked for a task so an event control such as @(s(a, b)) inside an automatic
// task is reached. §9.4.2.4: arguments to a sequence used in an event control
// shall be static, so an automatic task local passed as a sequence argument is
// an error (in_automatic is false for a process block and a non-automatic
// task, so static sequence arguments stay legal there).
static void WalkItemForSequenceEvents(
    const ModuleItem* item,
    const std::unordered_set<std::string_view>& seq_names,
    const SequenceDeclMap& seq_decls, DiagEngine& diag) {
  if (IsProcessBlockItem(item->kind)) {
    if (item->body) {
      WalkStmtsForSequenceEvents(const_cast<Stmt*>(item->body), seq_names,
                                 seq_decls, false, diag);
    }
    return;
  }
  if (item->kind != ModuleItemKind::kTaskDecl) return;
  if (item->body) {
    WalkStmtsForSequenceEvents(const_cast<Stmt*>(item->body), seq_names,
                               seq_decls, item->is_automatic, diag);
  }
  for (auto* s : item->func_body_stmts) {
    WalkStmtsForSequenceEvents(s, seq_names, seq_decls, item->is_automatic,
                               diag);
  }
}

void Elaborator::ValidateSequenceEventArgs(const ModuleDecl* decl) {
  if (sequence_names_.empty()) return;
  // §16.8 actual-argument checks need each named sequence's formals, so map the
  // sequences declared in this scope by name. A sequence instantiated across a
  // scope boundary is absent here, and its count check is simply skipped.
  SequenceDeclMap seq_decls;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kSequenceDecl) {
      seq_decls[item->name] = item;
    }
  }
  for (const auto* item : decl->items) {
    WalkItemForSequenceEvents(item, sequence_names_, seq_decls, diag_);
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

static void CheckDeferredCallRefArgs(
    const Stmt* action, const DeferredSubroutineMap& subs,
    const std::unordered_set<std::string_view>& auto_vars, DiagEngine& diag) {
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
    // §16.4: a dynamic variable (e.g. a class property, reached through a
    // member access) cannot be the actual for a pass-by-reference formal.
    if (a->kind == ExprKind::kMemberAccess) {
      diag.Error(
          a->range.start,
          std::format("§16.4: cannot pass dynamic variable as actual for "
                      "ref{} formal '{}' in deferred-assertion call",
                      formals[i].is_const ? " const" : "", formals[i].name));
      continue;
    }
    // §16.4: an automatic variable is likewise disallowed as the actual for a
    // pass-by-reference formal, because its storage may no longer exist when
    // the deferred action runs. A bare identifier naming an automatic variable
    // in scope -- a formal or local of the enclosing automatic subroutine -- is
    // an error.
    if (a->kind == ExprKind::kIdentifier &&
        auto_vars.find(a->text) != auto_vars.end()) {
      diag.Error(
          a->range.start,
          std::format("§16.4: cannot pass automatic variable as actual for "
                      "ref{} formal '{}' in deferred-assertion call",
                      formals[i].is_const ? " const" : "", formals[i].name));
    }
  }
}

static void CheckDeferredActionStmt(
    const Stmt* s, const DeferredSubroutineMap& subs,
    const std::unordered_set<std::string_view>& auto_vars, DiagEngine& diag) {
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

  CheckDeferredCallRefArgs(s->assert_pass_stmt, subs, auto_vars, diag);
  CheckDeferredCallRefArgs(s->assert_fail_stmt, subs, auto_vars, diag);
}

// §16.4: gather the names of automatic variables visible to deferred assertions
// in a subroutine body. When the enclosing task or function has automatic
// lifetime, every local variable is automatic; an explicitly-automatic local is
// automatic even inside a static routine.
static void CollectAutomaticVarNames(
    const Stmt* s, bool routine_is_automatic,
    std::unordered_set<std::string_view>& out) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl &&
      (routine_is_automatic || s->var_is_automatic)) {
    out.insert(s->var_name);
  }
  for (auto* sub : s->stmts)
    CollectAutomaticVarNames(sub, routine_is_automatic, out);
  CollectAutomaticVarNames(s->then_branch, routine_is_automatic, out);
  CollectAutomaticVarNames(s->else_branch, routine_is_automatic, out);
  CollectAutomaticVarNames(s->body, routine_is_automatic, out);
  CollectAutomaticVarNames(s->for_body, routine_is_automatic, out);
  CollectAutomaticVarNames(s->assert_pass_stmt, routine_is_automatic, out);
  CollectAutomaticVarNames(s->assert_fail_stmt, routine_is_automatic, out);
  for (const auto& ci : s->case_items)
    CollectAutomaticVarNames(ci.body, routine_is_automatic, out);
}

void Elaborator::WalkStmtsForDeferredActions(
    const Stmt* s, const std::unordered_set<std::string_view>& auto_vars) {
  if (!s) return;
  CheckDeferredActionStmt(s, deferred_subroutine_map_, auto_vars, diag_);
  for (auto* sub : s->stmts) WalkStmtsForDeferredActions(sub, auto_vars);
  WalkStmtsForDeferredActions(s->then_branch, auto_vars);
  WalkStmtsForDeferredActions(s->else_branch, auto_vars);
  WalkStmtsForDeferredActions(s->body, auto_vars);
  WalkStmtsForDeferredActions(s->for_body, auto_vars);
  WalkStmtsForDeferredActions(s->assert_pass_stmt, auto_vars);
  WalkStmtsForDeferredActions(s->assert_fail_stmt, auto_vars);
  for (const auto& ci : s->case_items)
    WalkStmtsForDeferredActions(ci.body, auto_vars);
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
    // A task or function keeps its body in func_body_stmts; procedural blocks
    // (initial/always) keep theirs in body. Validate whichever this item uses.
    if (!item->body && item->func_body_stmts.empty()) continue;
    // §16.4: collect the automatic-variable names in scope for this item so a
    // deferred action call passing one of them by reference can be rejected. An
    // automatic task or function makes its formals and locals automatic.
    bool routine_is_automatic = (item->kind == ModuleItemKind::kTaskDecl ||
                                 item->kind == ModuleItemKind::kFunctionDecl) &&
                                item->is_automatic;
    std::unordered_set<std::string_view> auto_vars;
    if (routine_is_automatic) {
      for (const auto& fa : item->func_args) auto_vars.insert(fa.name);
    }
    CollectAutomaticVarNames(item->body, routine_is_automatic, auto_vars);
    for (const auto* st : item->func_body_stmts) {
      CollectAutomaticVarNames(st, routine_is_automatic, auto_vars);
    }
    WalkStmtsForDeferredActions(item->body, auto_vars);
    for (const auto* st : item->func_body_stmts) {
      WalkStmtsForDeferredActions(st, auto_vars);
    }
  }
}

}  // namespace delta
