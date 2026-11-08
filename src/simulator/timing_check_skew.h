#pragma once

#include <cstddef>

namespace delta {

class SimContext;
class SpecifyManager;

void ArmSkewWindow(const SpecifyManager& mgr, std::size_t index,
                   SimContext& ctx);

}  // namespace delta
