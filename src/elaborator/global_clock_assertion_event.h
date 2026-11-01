#ifndef DELTA_ELABORATOR_GLOBAL_CLOCK_ASSERTION_EVENT_H
#define DELTA_ELABORATOR_GLOBAL_CLOCK_ASSERTION_EVENT_H

#include <cstddef>
#include <string_view>
#include <vector>

#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"

namespace delta {

class Arena;

// §16.5.2: a concurrent assertion whose leading clocking event is
// $global_clock is clocked by the clocking event of the global clocking
// declaration in scope. The clause states the equivalence outright: given
// `global clocking @clk; endclocking`, `assert property(@$global_clock a);` is
// logically equivalent to `assert property(@clk a);`.

// §16.5.2: whether `sensitivity` is the single clocking event $global_clock.
bool IsGlobalClockLeadingEvent(const std::vector<EventExpr>& sensitivity);

// §16.5.2: rewrite a $global_clock leading clocking event into the clocking
// event of the global clocking declaration, which is what gives the assertion
// the clock the equivalence above names. Returns whether the rewrite was made.
// A sensitivity that is not $global_clock is left as it stands, and so is one
// offered an empty `global_event`: §14.14 reports a $global_clock reference
// with no global clocking declaration in scope, and this leaves that report the
// only account of it. A gate written on the $global_clock event
// (`@($global_clock iff en)`, the gated clock of the same clause) is carried
// onto each substituted event that carries no gate of its own.
bool SubstituteGlobalClockLeadingEvent(
    std::vector<EventExpr>& sensitivity,
    const std::vector<EventExpr>& global_event);

// §14.14: $global_clock refers explicitly to the event expression of the
// effective global clocking declaration, and an event control naming it waits
// on that event expression wherever it is written -- a procedure's own
// sensitivity list, an event control standing as a statement, an
// intra-assignment event control, a wait.
// Walk the statement tree rooted at `stmt` and rewrite every such event control
// into `global_event`, by the same substitution
// SubstituteGlobalClockLeadingEvent makes on a leading clocking event, so the
// process suspends on the declared event rather than on a system call naming no
// signal. A concurrent assertion's leading clock written as $global_clock is
// rewritten the same way (§16.5.2).
//
// Returns the statement tree to use, which is `stmt` itself where nothing was
// rewritten -- where no event control named $global_clock, and where
// `global_event` is empty. No statement reachable from `stmt` is written to. A
// statement whose event control is rewritten is copied into `arena` first, and
// so is every statement on the path from `stmt` down to it, because each of
// those holds a pointer to the next. A subtree holding no $global_clock event
// control is returned as it stands, and nothing is allocated for it.
//
// The copy is what lets two callers holding the same Stmt objects substitute
// different `global_event`s into them. A statement rewritten in place would
// carry the first caller's substitution into the second caller's result, so
// keep any further rewrite of a statement tree here on a copy as well.
//
// `global_event` is the effective global clocking declaration's event
// expression, which EffectiveGlobalClockingEvent below computes for both of
// §14.14's lookup rules.
Stmt* SubstituteGlobalClockEventControls(
    Stmt* stmt, const std::vector<EventExpr>& global_event, Arena& arena);

// §14.14: $global_clock in an actual argument of a checker instance resolves
// where the actual is substituted, which is inside the checker, so a clocking
// event $global_clock written in a sequence or property actual,
// `@($global_clock) a`, waits on the checker's effective global clocking's
// event `global_event`. Returns `actual` itself where its tree writes no such
// event, or `global_event` is empty; otherwise a copy whose tree is its own,
// rewritten as SubstituteGlobalClockLeadingEvent rewrites a leading clock.
Expr* SubstituteGlobalClockInActual(Expr* actual,
                                    const std::vector<EventExpr>& global_event,
                                    Arena& arena);

// §14.14: $global_clock in an actual argument of a sequence or property
// instance resolves where the instance is used, so the instance `call`, a
// whole assertion spec, waits on the event `global_event` of the scope that
// asserts it. Returns `call` itself where no actual writes such an event;
// otherwise a copy whose actuals SubstituteGlobalClockInActual rewrote.
Expr* SubstituteGlobalClockInInstanceActuals(
    Expr* call, const std::vector<EventExpr>& global_event, Arena& arena);

// §14.14 lookup rule b): a $global_clock reference in a scope that declares no
// global clocking of its own resolves against the declaration of the nearest
// enclosing instance, the result being that declaration's event expression.
// That event expression names signals of the scope that declares it, so a
// reference in a descendant waits on the declaring instance's signals and not
// on names of its own.
//
// Returns the event expression to substitute at a reference in the instance
// `referencing_inst_path` names, given the nearest declaration's event
// expression `declared_events` in the instance `declaring_inst_path` names.
// Both paths are ElaboratorData::current_inst_path_: the instance names from
// the top-level hierarchy block down, joined by dots, with the top-level
// hierarchy block's own name as the first component.
//
// Returns `declared_events` unchanged where the two paths are equal, which is
// rule a): the declaration is in the scope holding the reference, so its event
// expression already names signals that scope can see.
//
// Returns nullptr where `declared_events` is null.
//
// Otherwise the result is a new vector allocated from `arena`, holding a copy
// of each event in which a signal that is a plain identifier is replaced by
// the §23.6 hierarchical name reaching it from the top-level hierarchy block:
// `clk` declared in instance `sub1` becomes `sub1.clk`. Where the declaration
// is in the top-level hierarchy block itself there is no instance name to
// reach it through, and the name written is §23.6's `$root.clk`, absolute from
// the top of the instantiated design.
const std::vector<EventExpr>* EffectiveGlobalClockingEvent(
    const std::vector<EventExpr>* declared_events,
    std::string_view declaring_inst_path,
    std::string_view referencing_inst_path, Arena& arena);

// §14.14 with §17.3: $global_clock in the sequence and property `actuals` of
// the checker instance at `checker_inst_path` is the checker's effective
// global clocking's event, its names written as the scope instantiating the
// checker reaches them, since the actuals' names stand there. Each actual is
// replaced by its rewritten copy. The nearest declaration is the last of
// `scopes`, each holding a declaration's `events` and the `inst_path` of the
// instance declaring it; with none, the actuals are left as they are.
template <typename Scope>
void ResolveGlobalClockInCheckerActuals(ActualsByFormal& actuals,
                                        const std::vector<Scope>& scopes,
                                        std::string_view checker_inst_path,
                                        Arena& arena) {
  if (scopes.empty()) return;
  size_t last_dot = checker_inst_path.rfind('.');
  std::string_view parent = checker_inst_path.substr(
      0, last_dot == std::string_view::npos ? 0 : last_dot);
  const std::vector<EventExpr>* in_parent = EffectiveGlobalClockingEvent(
      scopes.back().events, scopes.back().inst_path, parent, arena);
  for (auto& entry : actuals) {
    entry.second =
        SubstituteGlobalClockInActual(entry.second, *in_parent, arena);
  }
}

}  // namespace delta

#endif  // DELTA_ELABORATOR_GLOBAL_CLOCK_ASSERTION_EVENT_H
