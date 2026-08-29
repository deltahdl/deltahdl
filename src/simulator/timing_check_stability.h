#pragma once

#include <cstddef>

namespace delta {

class SimContext;
class SpecifyManager;

// Arms the watchers one of §31.3's four remaining stability checks needs:
// §31.3.3's $setuphold, §31.3.4's $removal, §31.3.5's $recovery and §31.3.6's
// $recrem. `index` is a position in SpecifyManager::GetTimingChecks, and the
// entry there has to be one of those four kinds.
//
// §31.3.1's $setup and §31.3.2's $hold are armed by
// simulator/timing_check_driver.cpp instead. They are one-limit checks whose
// window lies wholly on one side of the reference edge, where these four
// either carry two limits bounding a window on both sides or place the
// reference edge at the opposite end from $setup's.
//
// Nothing is armed when either signal names no variable of the design, which is
// what a check whose specify block was registered for a module the design never
// elaborated leaves behind.
void ArmStabilityPair(const SpecifyManager& mgr, std::size_t index,
                      SimContext& ctx);

}  // namespace delta
