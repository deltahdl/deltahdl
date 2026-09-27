#pragma once

// §31.9.1 and §31.9.4: the delayed_reference and delayed_data signals a
// $setuphold or $recrem names, driven from the signals they are copies of.

namespace delta {

class Arena;
class SimContext;
class SpecifyManager;

// Drives every delayed signal a registered $setuphold or $recrem names from its
// original, the whole run long. Without negative-value handling in force the
// copy follows at once (§31.9.4); with it, the copy lags by the delay §31.9.1
// computes for its original. Defined in
// simulator/timing_check_delayed_signals.cpp.
void DriveTimingCheckDelayedSignals(const SpecifyManager& mgr, SimContext& ctx,
                                    Arena& arena);

}  // namespace delta
