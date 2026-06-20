#pragma once

#include <cstdint>

#include "synthesizer/aig.h"
#include "synthesizer/lut_map.h"

namespace delta {

uint32_t RetimeForward(AigGraph& g);
uint32_t RetimeBackward(AigGraph& g);

LutMapping MapForDelay(const AigGraph& g, uint32_t lut_size);

LutMapping IterativeAreaDelay(const AigGraph& g, uint32_t lut_size,
                              uint32_t iterations);

}  // namespace delta
