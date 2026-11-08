#pragma once

#include <cstdint>

#include "common/types.h"
#include "simulator/net.h"

namespace delta {

class Arena;

Strength StrengthFromParserCode(uint8_t s);

Logic4Vec ApplyHighzStrengthsToValue(const Logic4Vec& val, DriverStrength ds,
                                     Arena& arena);

}  // namespace delta
