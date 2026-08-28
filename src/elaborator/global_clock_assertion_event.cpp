#include "elaborator/global_clock_assertion_event.h"

#include <cstddef>
#include <vector>

#include "common/arena.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

namespace delta {

bool IsGlobalClockLeadingEvent(const std::vector<EventExpr>& sensitivity) {
  if (sensitivity.size() != 1) return false;
  const Expr* signal = sensitivity.front().signal;
  return signal != nullptr && signal->kind == ExprKind::kSystemCall &&
         signal->callee == "$global_clock";
}

bool SubstituteGlobalClockLeadingEvent(
    std::vector<EventExpr>& sensitivity,
    const std::vector<EventExpr>& global_event) {
  if (global_event.empty()) return false;
  if (!IsGlobalClockLeadingEvent(sensitivity)) return false;
  Expr* gate = sensitivity.front().iff_condition;
  sensitivity = global_event;
  for (auto& ev : sensitivity) {
    if (ev.iff_condition == nullptr) ev.iff_condition = gate;
  }
  return true;
}

namespace {

// One statement of the tree being rewritten, and the statement a rewrite is
// written into. `original` is never written to. `Mutable` returns a copy of
// `original` allocated from `arena`, making it on the first call and returning
// that same copy on every later one, so a statement is copied only once and
// only when something in it or beneath it is actually rewritten. `current` is
// `original` until then, which is what leaves a subtree holding no
// $global_clock event control shared rather than copied.
struct CloneOnWriteStmt {
  Stmt* original;
  Stmt* current;
  Arena& arena;

  Stmt* Mutable() {
    if (current == original) current = arena.Create<Stmt>(*original);
    return current;
  }
};

using StmtSlot = Stmt* Stmt::*;
using StmtListSlot = std::vector<Stmt*> Stmt::*;

// Rewrite the statement `slot` names, and write the result into the owner's
// copy where the rewrite produced a different statement.
void SubstituteInStmtSlot(CloneOnWriteStmt& owner,
                          const std::vector<EventExpr>& global_event,
                          StmtSlot slot) {
  Stmt* sub = owner.original->*slot;
  Stmt* rewritten =
      SubstituteGlobalClockEventControls(sub, global_event, owner.arena);
  if (rewritten != sub) owner.Mutable()->*slot = rewritten;
}

// Rewrite every statement of the list `slot` names, and write each result into
// the owner's copy of the list where the rewrite produced a different
// statement.
void SubstituteInStmtListSlot(CloneOnWriteStmt& owner,
                              const std::vector<EventExpr>& global_event,
                              StmtListSlot slot) {
  const std::vector<Stmt*>& subs = owner.original->*slot;
  for (size_t i = 0; i < subs.size(); ++i) {
    Stmt* rewritten =
        SubstituteGlobalClockEventControls(subs[i], global_event, owner.arena);
    if (rewritten != subs[i]) (owner.Mutable()->*slot)[i] = rewritten;
  }
}

// Rewrite the body of every case item, which is a nested statement reached
// through Stmt::case_items rather than through a slot of Stmt itself.
void SubstituteInCaseItems(CloneOnWriteStmt& owner,
                           const std::vector<EventExpr>& global_event) {
  const std::vector<CaseItem>& items = owner.original->case_items;
  for (size_t i = 0; i < items.size(); ++i) {
    Stmt* rewritten = SubstituteGlobalClockEventControls(
        items[i].body, global_event, owner.arena);
    if (rewritten != items[i].body) {
      owner.Mutable()->case_items[i].body = rewritten;
    }
  }
}

// Recurse into every nested-statement slot of the statement `owner` holds, so
// that an event control written anywhere beneath a procedure is reached.
void SubstituteGlobalClockInSubStmts(
    CloneOnWriteStmt& owner, const std::vector<EventExpr>& global_event) {
  SubstituteInStmtListSlot(owner, global_event, &Stmt::stmts);
  SubstituteInStmtListSlot(owner, global_event, &Stmt::for_inits);
  SubstituteInStmtListSlot(owner, global_event, &Stmt::for_steps);
  SubstituteInStmtListSlot(owner, global_event, &Stmt::fork_stmts);
  SubstituteInCaseItems(owner, global_event);
  SubstituteInStmtSlot(owner, global_event, &Stmt::then_branch);
  SubstituteInStmtSlot(owner, global_event, &Stmt::else_branch);
  SubstituteInStmtSlot(owner, global_event, &Stmt::body);
  SubstituteInStmtSlot(owner, global_event, &Stmt::for_body);
}

}  // namespace

Stmt* SubstituteGlobalClockEventControls(
    Stmt* stmt, const std::vector<EventExpr>& global_event, Arena& arena) {
  // An empty `global_event` substitutes nothing, so the whole walk is skipped
  // rather than run to no effect: §14.14 reports a $global_clock reference with
  // no global clocking declaration in scope, and this leaves that report the
  // only account of it.
  if (stmt == nullptr || global_event.empty()) return stmt;
  CloneOnWriteStmt owner{stmt, stmt, arena};
  if (IsGlobalClockLeadingEvent(stmt->events)) {
    SubstituteGlobalClockLeadingEvent(owner.Mutable()->events, global_event);
  }
  SubstituteGlobalClockInSubStmts(owner, global_event);
  return owner.current;
}

}  // namespace delta
