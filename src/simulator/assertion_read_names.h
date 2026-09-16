#pragma once

#include <string>
#include <unordered_set>

#include "common/arena.h"
#include "parser/ast.h"

namespace delta {

class SimContext;

// §16.5.1: the names a concurrent assertion's property reads, which the
// lowerer enrols in the sampled-value store so that the property is
// evaluated against each variable's value at the end of the time slot
// rather than whatever stands at the clock tick.

// The names an expression a sampled value is taken of reads: what the
// reader-name walk §9.2.2.2.1's implicit sensitivity list is built from
// answers, and each hierarchical reference (§23.6) under its dotted
// spelling, the name a child instance's variable is keyed under.
void CollectSampledOperandNames(const Expr* e,
                                std::unordered_set<std::string>& out);

// §16.12.2: the names a named sequence's flattened body reads, the
// sequences it instantiates included.
void CollectSequenceReadNames(const ModuleItem* seq, SimContext& ctx,
                              Arena& arena,
                              std::unordered_set<std::string>& names);

// §16.12.4 and §16.12.5: the names every operand of a property of operands
// reads; §16.12.17: an instance of a named property reads what the body
// reads, so the body is walked too, to a depth that reads a recursive body
// once; §16.12.18: a sequence or a property passed as an actual argument is
// read by the instance, so it is walked with the instance.
void CollectPropertyTreeReadNames(const PropertyExprNode* node, SimContext& ctx,
                                  Arena& arena,
                                  std::unordered_set<std::string>& names);

}  // namespace delta
