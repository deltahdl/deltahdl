#pragma once

#include <cstdint>
#include <vector>

#include "common/types.h"
#include "simulator/net.h"

namespace delta {

bool AnyDriverUnknownAt(const std::vector<Logic4Vec>& drivers, uint32_t bit);

bool AnyDriverRangedAt(const std::vector<Logic4Vec>& drivers,
                       const std::vector<DriverStrength>& strengths,
                       uint32_t bit);

uint8_t ResolveBitOverDriverStates(const std::vector<Logic4Vec>& drivers,
                                   const std::vector<DriverStrength>& strengths,
                                   NetType type, uint32_t bit,
                                   NetStrength& out);

}  // namespace delta
