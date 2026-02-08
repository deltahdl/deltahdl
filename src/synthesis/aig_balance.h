#pragma once

#include "synthesis/aig.h"

namespace delta {

// --- AIG balancing pass ---
//
// Restructures tree-like AND/OR cones to minimize the critical path
// depth. Multi-input AND trees are collected, flattened, and rebuilt
// as balanced binary trees. This reduces the number of AIG levels,
// directly improving circuit delay.
//
// This corresponds to ABC's "balance" command.

class AigBalancer {
 public:
  /// Run AIG balancing on the graph.
  /// Restructures associative cones for minimum depth.
  void balance(AigGraph& graph);
};

}  // namespace delta
