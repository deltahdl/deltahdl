#pragma once

#include <cstddef>
#include <unordered_map>

#include "simulator/vpi_object.h"

namespace delta {

class SimContext;

void VpiPutRunDelays(
    VpiObject& obj,
    const std::unordered_map<const VpiObject*, std::size_t>& run_entries,
    SimContext& sim);

}  // namespace delta
