#pragma once

#include "synthesis/aig.h"

namespace delta {

/// Constant propagation: replace outputs that are provably constant.
void ConstProp(AigGraph& g);

/// AIG balancing: reduce critical path depth by restructuring AND trees.
void Balance(AigGraph& g);

/// AIG rewriting: local subgraph replacement using cut enumeration.
void Rewrite(AigGraph& g);

/// AIG refactoring: larger-scope restructuring for area reduction.
void Refactor(AigGraph& g);

/// Redundancy removal: identify and remove stuck-at-fault redundant nodes.
void RemoveRedundancy(AigGraph& g);

}  // namespace delta
