#pragma once

#include <cstdint>
#include <vector>

#include "synthesis/aig.h"

namespace delta {

// --- K-LUT Technology Mapping ---
//
// Maps an And-Inverter Graph to a network of K-input lookup tables (LUTs).
// Each LUT implements an arbitrary Boolean function of up to K inputs.
// For K <= 6, the truth table fits in a uint64_t (2^6 = 64 rows).

/// A single LUT cell in the mapped netlist.
struct LutCell {
  uint32_t output = 0;           // AIG node id of the LUT output
  std::vector<uint32_t> inputs;  // AIG input node ids (up to K)
  uint64_t truth_table = 0;      // Truth table encoding (K <= 6)
};

/// Result of LUT mapping: a set of LUT cells covering all outputs.
struct LutMapping {
  std::vector<LutCell> cells;
  uint32_t lut_size = 4;  // K
};

/// A cut: a set of leaf node ids that form the inputs to a subgraph
/// rooted at a given node.
struct Cut {
  std::vector<uint32_t> leaves;  // AIG node ids (not literals)
};

/// K-LUT mapper. Enumerates priority cuts for each AIG node and selects
/// an area-oriented covering to produce LUT cells for every output.
class LutMapper {
 public:
  explicit LutMapper(uint32_t lut_size = 4);

  /// Map the given AIG graph to a LUT network.
  LutMapping Map(const AigGraph& aig);

 private:
  uint32_t lut_size_;
};

}  // namespace delta
