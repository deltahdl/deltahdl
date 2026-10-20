#pragma once

#include <cstddef>
#include <unordered_map>

#include "simulator/vpi_object.h"

namespace delta {

class SimContext;

// §38.32: file the delays vpi_put_delays set on `obj` with the run `sim`, so
// that its next transitions and checks take them: a module path's with the
// run's path, a timing check's limits with the run's check -- each the entry
// `run_entries` gives the object's place of among the specify manager's -- and
// a gate's or udp's rise, fall and turn-off delays with the primitive driving
// its output. Any other object is left to its own handling.
void VpiPutRunDelays(
    VpiObject& obj,
    const std::unordered_map<const VpiObject*, std::size_t>& run_entries,
    SimContext& sim);

}  // namespace delta
