#pragma once

#include <cstdint>
#include <vector>

#include "simulator/coverage_types.h"

namespace delta {

bool IsInValueSet(const std::vector<int64_t>& set, int64_t val);

bool BinParticipates(const CoverBin& bin);

}  // namespace delta
