#pragma once

#include "synth/aig.h"

namespace delta {

// --- AIG refactoring pass ---
//
// Recomputes node functions using larger cuts (typically 10-16 inputs)
// and re-synthesizes each cut cone from scratch using BDD-based or
// SOP-based decomposition. Unlike rewriting, which matches small
// patterns, refactoring can discover global restructuring opportunities.
//
// This corresponds to ABC's "refactor" command.

class AigRefactor {
public:
    /// Run one pass of AIG refactoring on the graph.
    void refactor(AigGraph& graph);
};

} // namespace delta
