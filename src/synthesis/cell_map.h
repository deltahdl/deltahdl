#pragma once

#include "synthesis/aig.h"

namespace delta {

// Forward declaration — full definition in liberty.h.
struct CellLibrary;

// --- ASIC standard cell mapping ---
//
// Maps an AIG onto gates from a standard cell library. Uses
// tree-based pattern matching with supergate generation to
// cover the AIG with library cells while optimizing for area
// and delay.

class CellMapper {
 public:
  /// Map the AIG onto standard cells from the given library.
  void map(AigGraph& graph, const CellLibrary& lib);
};

}  // namespace delta
