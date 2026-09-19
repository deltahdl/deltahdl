#pragma once

#include <vector>

#include "parser/ast_stmt.h"

namespace delta {

class PropertyRegistry;

// §16.16.1: the set of semantic leading clocks of a multiclocked property,
// defined on its structure with `inherited` standing for the clock flowing
// in from outside: a sequence's is its own leading clock, a property with
// none is inherited, an operand written under a clocking event of its own
// replaces inherited by that event, not, accept_on and reject_on take
// their operand's, and and or the union of their operands', an
// implication its antecedent's, an instance the body's, and the other
// operators, if, case, nexttime, always, eventually, until and the
// synchronous aborts, are inherited. `outer` is the incoming outer clock,
// the statement's leading clocking event, which inherited refers to, so the
// set answered names no inherited clock; each clock stands in it once, two
// being the same where they are written the same, the clause having
// identical rather than equal clocks make one.
std::vector<EventExpr> SemanticLeadingClocks(
    const PropertyExprNode* node, const std::vector<EventExpr>& outer,
    const PropertyRegistry& registry);

// §16.16 (e): whether the property's semantic leading clock is unique, the
// set holding one clock, which an assertion statement whose maximal
// property is multiclocked requires.
bool HasUniqueSemanticLeadingClock(const PropertyExprNode* node,
                                   const std::vector<EventExpr>& outer,
                                   const PropertyRegistry& registry);

// Whether every clocking event the tree names, on an operand, in a sequence
// or in a declaration it instantiates, is identical to `clock`: §16.16 (c)
// lets a multiclocked property take no contextually inferred leading
// clocking event, an operand clocked as the inferred clock is being no
// other clock.
bool TreeNamesOnlyClock(const PropertyExprNode* node,
                        const std::vector<EventExpr>& clock,
                        const PropertyRegistry& registry);

}  // namespace delta
