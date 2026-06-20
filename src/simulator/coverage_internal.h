#pragma once

#include <cstdint>
#include <vector>

#include "simulator/coverage.h"

namespace delta {

// Internal helpers shared across the coverage translation units. They are
// declared here and defined exactly once in coverage.cpp.

// True when `val` appears anywhere in `set`.
bool IsInValueSet(const std::vector<int64_t>& set, int64_t val);

// Whether a coverpoint bin contributes to the coverpoint's coverage numerator
// and denominator. Illegal, ignore, and default bins never contribute (LRM
// 19.5/19.5.6), and a bin with no associated value or transition is excluded
// from both the numerator and the denominator (LRM 19.11.1).
bool BinParticipates(const CoverBin& bin);

}  // namespace delta
