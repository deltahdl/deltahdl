#pragma once

#include <vector>

#include "elaborator/rtlir.h"

namespace delta {

class Arena;
class SimContext;

bool SplitNetArrayContAssign(const RtlirContAssign& ca, SimContext& ctx,
                             Arena& arena,
                             std::vector<RtlirContAssign>& pieces);

}  // namespace delta
