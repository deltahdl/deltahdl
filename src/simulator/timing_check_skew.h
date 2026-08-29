#pragma once

#include <cstddef>

namespace delta {

class SimContext;
class SpecifyManager;

// Arms the watchers one of §31.4's three skew checks needs: §31.4.1's $skew,
// §31.4.2's $timeskew and §31.4.3's $fullskew. `index` is a position in
// SpecifyManager::GetTimingChecks, and the entry there has to be one of those
// three kinds.
//
// A skew check measures how far apart two signals move rather than placing one
// signal's transition inside a window the other bounds, so neither signal is
// the timestamp and neither is the timecheck in §31.3's sense. That is what
// separates these from the stability windows of
// simulator/timing_check_stability.h.
//
// Nothing is armed when either signal names no variable of the design, which is
// what a check whose specify block was registered for a module the design never
// elaborated leaves behind.
void ArmSkewWindow(const SpecifyManager& mgr, std::size_t index,
                   SimContext& ctx);

}  // namespace delta
