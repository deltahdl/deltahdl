#pragma once

#include <optional>

#include "common/types.h"
#include "simulator/net.h"

namespace delta {

class Arena;
class Scheduler;

std::optional<Logic4Vec> SettleTriregCharge(Net& net, Arena& arena,
                                            Scheduler* sched);

Logic4Vec TriregStoredCharge(const Net& net, Arena& arena);

}  // namespace delta
