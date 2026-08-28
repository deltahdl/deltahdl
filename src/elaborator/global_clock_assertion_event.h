#ifndef DELTA_ELABORATOR_GLOBAL_CLOCK_ASSERTION_EVENT_H
#define DELTA_ELABORATOR_GLOBAL_CLOCK_ASSERTION_EVENT_H

#include <vector>

#include "parser/ast_stmt.h"

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

// §14.14: "The $global_clock system function shall be used to explicitly
// refer to the event expression in the effective global clocking
// declaration", and an event control naming it waits on that event expression
// wherever it is written -- a procedure's own sensitivity list, an event
// control standing as a statement, an intra-assignment event control, a wait.
// Walk the statement tree rooted at `stmt` and rewrite every such event
// control into `global_event`, by the same substitution
// SubstituteGlobalClockLeadingEvent makes on a leading clocking event, so the
// process suspends on the declared event rather than on a system call naming
// no signal.
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
// This serves §14.14 lookup rule a) alone, whose result is "the event
// expression of that global clocking declaration" in "the enclosing module,
// interface, checker, or program instance scope": the caller passes the
// enclosing module's own declaration. Rule b), which walks up the instance
// hierarchy to an ancestor's declaration, is not served here, and a reference
// resolving to an ancestor's event is left as it stands rather than half
// resolved.
Stmt* SubstituteGlobalClockEventControls(
    Stmt* stmt, const std::vector<EventExpr>& global_event, Arena& arena);

}  // namespace delta

#endif  // DELTA_ELABORATOR_GLOBAL_CLOCK_ASSERTION_EVENT_H
