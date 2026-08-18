#ifndef DELTA_ELABORATOR_GLOBAL_CLOCK_ASSERTION_EVENT_H
#define DELTA_ELABORATOR_GLOBAL_CLOCK_ASSERTION_EVENT_H

#include <vector>

#include "parser/ast_stmt.h"

namespace delta {

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

}  // namespace delta

#endif  // DELTA_ELABORATOR_GLOBAL_CLOCK_ASSERTION_EVENT_H
