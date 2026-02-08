#pragma once

#include "synthesis/aig.h"

#include <cstdint>
#include <vector>

namespace delta {

// --- FPGA LUT mapping ---
//
// Maps an AIG onto a network of k-input lookup tables (LUTs) using
// priority-cut based technology mapping. The default LUT size is 6,
// matching modern Xilinx/Intel FPGA architectures.

struct LutCell {
    std::vector<uint32_t> inputs;  // AIG literals feeding this LUT
    uint64_t truth_table = 0;      // k-LUT truth table (up to 6 inputs)
};

struct LutMapping {
    std::vector<LutCell> cells;
    uint32_t lut_size = 6;
    uint32_t depth = 0;   // critical path depth in LUT levels
    uint32_t area = 0;    // total number of LUTs used
};

class LutMapper {
public:
    explicit LutMapper(uint32_t lut_size = 6);

    /// Map an AIG to a LUT network.
    LutMapping map(const AigGraph& graph);

private:
    uint32_t lut_size_;
};

} // namespace delta
