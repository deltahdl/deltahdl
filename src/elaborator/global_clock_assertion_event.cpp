#include "elaborator/global_clock_assertion_event.h"

#include <vector>

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

// Recurse into every nested-statement slot of `s`, so that an event control
// written anywhere beneath a procedure is reached.
void SubstituteGlobalClockInSubStmts(
    Stmt* s, const std::vector<EventExpr>& global_event) {
  for (auto* sub : s->stmts) {
    SubstituteGlobalClockEventControls(sub, global_event);
  }
  for (auto* sub : s->for_inits) {
    SubstituteGlobalClockEventControls(sub, global_event);
  }
  for (auto* sub : s->for_steps) {
    SubstituteGlobalClockEventControls(sub, global_event);
  }
  for (auto* sub : s->fork_stmts) {
    SubstituteGlobalClockEventControls(sub, global_event);
  }
  for (auto& ci : s->case_items) {
    SubstituteGlobalClockEventControls(ci.body, global_event);
  }
  SubstituteGlobalClockEventControls(s->then_branch, global_event);
  SubstituteGlobalClockEventControls(s->else_branch, global_event);
  SubstituteGlobalClockEventControls(s->body, global_event);
  SubstituteGlobalClockEventControls(s->for_body, global_event);
}

}  // namespace

void SubstituteGlobalClockEventControls(
    Stmt* stmt, const std::vector<EventExpr>& global_event) {
  if (stmt == nullptr) return;
  SubstituteGlobalClockLeadingEvent(stmt->events, global_event);
  SubstituteGlobalClockInSubStmts(stmt, global_event);
}

}  // namespace delta
