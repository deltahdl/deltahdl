#pragma once

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/sequence_degeneracy.h"
#include "parser/ast.h"

namespace delta {

// §16.12.22: the class of matches a sequence admits, read off the lengths
// its matches can have: none where the operands of an intersect can have
// no length in common or an empty operand is fused by ##0 with another,
// empty alone where every operand is a repetition by zero, both where a
// repetition ranges from zero, and nonempty alone otherwise. An instance of
// a named sequence among the operands is read as the declaration's body,
// through `registry`, and a formal's reference as a boolean.
SequenceMatchClass ClassifySequenceMatches(const ModuleItem* seq,
                                           const PropertyRegistry& registry);

// §16.12.22: the restrictions on degenerate sequences applied over the
// property tree under `node`: a sequence used as a property shall be
// nondegenerate and admit no empty match (a), the antecedent of |-> shall
// be nondegenerate (b) and the antecedent of |=> shall admit at least one
// match (c); each breach is reported at `loc`.
void ValidateSequenceDegeneracy(const PropertyExprNode* node, SourceLoc loc,
                                const PropertyRegistry& registry,
                                DiagEngine& diag);

// §16.12.22 (a) over one sequence standing as a property.
void ValidateSequenceUsedAsProperty(const ModuleItem* seq, SourceLoc loc,
                                    const PropertyRegistry& registry,
                                    DiagEngine& diag);

}  // namespace delta
