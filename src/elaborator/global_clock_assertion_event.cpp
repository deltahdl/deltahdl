#include "elaborator/global_clock_assertion_event.h"

#include <cstddef>
#include <vector>

#include "common/arena.h"
#include "elaborator/elaborator_validate_internal.h"
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
  const Stmt* original;
  Stmt* current;
  Arena& arena;

  Stmt* Mutable() {
    if (current == original) current = arena.Create<Stmt>(*original);
    return current;
  }
};

// Recurse into every nested statement of the statement `owner` holds, so that
// an event control written anywhere beneath a procedure is reached. §14.14 says
// where $global_clock refers and not where it may be written, so every position
// a statement holds a statement in is one it may be written in.
//
// ForEachChildStmt in elaborator_validate_internal.h states those positions,
// once for the whole elaborator, which is why the list is not written out again
// here. It is walked twice so that the copy stays conditional. The first walk
// rewrites each nested statement of `owner.original` and records what came
// back. The second writes those results into `owner.Mutable()`, and runs only
// where some nested statement was actually rewritten. `owner.Mutable()` is a
// copy of `owner.original` and so has the same fields holding the same nested
// statements, and one function walks both, so the two walks reach the same
// positions in the same order and `next` names the position the result it
// consumes was recorded for.
void SubstituteGlobalClockInSubStmts(
    CloneOnWriteStmt& owner, const std::vector<EventExpr>& global_event) {
  std::vector<Stmt*> rewritten;
  bool any_rewritten = false;
  ForEachChildStmt(owner.original, [&](Stmt* const& sub) {
    Stmt* result =
        SubstituteGlobalClockEventControls(sub, global_event, owner.arena);
    if (result != sub) any_rewritten = true;
    rewritten.push_back(result);
  });
  if (!any_rewritten) return;
  size_t next = 0;
  ForEachChildStmt(owner.Mutable(),
                   [&](Stmt*& slot) { slot = rewritten[next++]; });
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
