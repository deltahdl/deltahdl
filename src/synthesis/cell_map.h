#pragma once

#include <string>
#include <vector>

#include "synthesis/aig.h"
#include "synthesis/liberty.h"

namespace delta {

// --- Standard-Cell Technology Mapping ---
//
// Maps an And-Inverter Graph to standard cells from a Liberty library.
// Matches small AIG subgraphs against cell function patterns (AND, OR, INV,
// etc.) and produces a netlist of cell instances.

/// A single cell instance in the mapped netlist.
struct CellInstance {
  std::string cell_name;
  std::vector<std::string> input_nets;
  std::string output_net;
};

/// Result of cell mapping: a set of cell instances covering all outputs.
struct CellMapping {
  std::vector<CellInstance> instances;
};

/// Standard-cell mapper. Matches AIG subgraphs against Liberty cell
/// functions and produces CellInstance entries for every output.
class CellMapper {
 public:
  explicit CellMapper(const Liberty& lib);

  /// Map the given AIG graph to standard cells.
  CellMapping Map(const AigGraph& aig) const;

 private:
  const Liberty& lib_;
};

}  // namespace delta
