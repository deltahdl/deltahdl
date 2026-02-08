#pragma once

#include "synthesis/aig.h"

namespace delta {

// --- AIG rewriting pass ---
//
// Replaces small subgraphs (typically 4-node cuts) with cheaper
// NPN-class equivalents drawn from a pre-computed table. This is
// the core optimization loop in AIG-based synthesis, analogous to
// ABC's "rewrite" command.
//
// The algorithm walks each internal node, computes its 4-input cut,
// evaluates the truth table, looks up the NPN class, and replaces
// the subgraph if a smaller implementation exists.

class AigRewriter {
public:
    /// Run one pass of AIG rewriting on the graph.
    /// May be called repeatedly until convergence.
    void rewrite(AigGraph& graph);
};

} // namespace delta
