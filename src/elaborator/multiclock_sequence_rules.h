#pragma once

#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/property_rewrite.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

// §16.13.1: the rules on a sequence built of subsequences on different
// clocks, applied over the sequences of the property tree under `node`,
// whose leading clock is `leading`: each maximal singly clocked subsequence
// shall admit only nonempty matches, differently clocked subsequences are
// joined by ##1 or ##0 alone, and differently clocked operands are combined
// by no other sequence operator; each breach is reported at `loc`.
void ValidateMulticlockSequences(const PropertyExprNode* node,
                                 const std::vector<EventExpr>& leading,
                                 SourceLoc loc,
                                 const PropertyRegistry& registry,
                                 DiagEngine& diag);

// The same over one sequence standing as a property.
void ValidateMulticlockSequence(const ModuleItem* seq,
                                const std::vector<EventExpr>& leading,
                                SourceLoc loc, const PropertyRegistry& registry,
                                DiagEngine& diag);

}  // namespace delta
