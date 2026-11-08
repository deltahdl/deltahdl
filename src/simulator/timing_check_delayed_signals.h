#pragma once

namespace delta {

class Arena;
class SimContext;
class SpecifyManager;

void DriveTimingCheckDelayedSignals(const SpecifyManager& mgr, SimContext& ctx,
                                    Arena& arena);

}  // namespace delta
