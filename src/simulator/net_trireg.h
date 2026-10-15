#pragma once

#include <optional>

#include "common/types.h"
#include "simulator/net.h"

namespace delta {

class Arena;
class Scheduler;

// §28.15.2 and §28.16.2: settles which bits of the trireg `net` are in the
// charge storage state as its sources now stand, schedules the charge decay
// of the bits entering it, and answers the charge the net drives with at its
// charge strength: the value it stores on those bits and z on the rest. None
// where no bit holds charge. Defined in simulator/net_trireg.cpp.
std::optional<Logic4Vec> SettleTriregCharge(Net& net, Arena& arena,
                                            Scheduler* sched);

// The charge the trireg `net` stores as it last settled: its value on every
// bit no source drives and z on the rest, which a switch carries on to the
// nets joined to it (§28.14).
Logic4Vec TriregStoredCharge(const Net& net, Arena& arena);

}  // namespace delta
