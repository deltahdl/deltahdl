#pragma once

#include <cstdint>

#include "synthesis/aig.h"
#include "synthesis/lut_map.h"

namespace delta {

// Register retiming: move latches across combinational logic to improve timing.
// Returns the number of latches moved.
uint32_t RetimeForward(AigGraph& g);
uint32_t RetimeBackward(AigGraph& g);

// Delay-oriented LUT mapping: minimize critical path depth.
LutMapping MapForDelay(const AigGraph& g, uint32_t lut_size);

// Iterative area-delay tradeoff: alternates between area and delay
// optimization. Returns the final mapping after `iterations` rounds.
LutMapping IterativeAreaDelay(const AigGraph& g, uint32_t lut_size,
                              uint32_t iterations);

}  // namespace delta
