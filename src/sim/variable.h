#pragma once

#include "common/types.h"

#include <cstdint>

namespace delta {

// --- Variable: storage for reg/logic/integer simulation objects ---

struct Variable {
    Logic4Vec value{};
    bool is_forced = false;
    Logic4Vec forced_value{};
};

} // namespace delta
