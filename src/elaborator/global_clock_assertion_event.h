#ifndef DELTA_ELABORATOR_GLOBAL_CLOCK_ASSERTION_EVENT_H
#define DELTA_ELABORATOR_GLOBAL_CLOCK_ASSERTION_EVENT_H

#include <string_view>
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
// `global_event` is the effective global clocking declaration's event
// expression, which EffectiveGlobalClockingEvent below computes for both of
// §14.14's lookup rules.
Stmt* SubstituteGlobalClockEventControls(
    Stmt* stmt, const std::vector<EventExpr>& global_event, Arena& arena);

// §14.14 lookup rule b): a $global_clock reference in a scope that declares no
// global clocking of its own resolves against the declaration of the nearest
// enclosing instance, "with the result being the event expression of that
// global clocking declaration". That event expression names signals of the
// scope that declares it, so a reference in a descendant waits on the
// declaring instance's signals and not on names of its own.
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

}  // namespace delta

#endif  // DELTA_ELABORATOR_GLOBAL_CLOCK_ASSERTION_EVENT_H
