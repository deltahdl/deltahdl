#pragma once

#include <string_view>
#include <vector>

#include "common/types.h"

namespace delta {

struct ArrayInfo;
class SimContext;
class Arena;

// Shared between eval_array.cpp and eval_array_locator.cpp. Defined once in
// eval_array.cpp.
std::vector<Logic4Vec> CollectVecElements(std::string_view var_name,
                                          const ArrayInfo& info,
                                          SimContext& ctx, Arena& arena);

}  // namespace delta
