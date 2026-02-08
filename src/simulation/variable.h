#pragma once

#include <cstdint>

#include "common/types.h"

namespace delta {

// --- Variable: storage for reg/logic/integer simulation objects ---

struct Variable {
  Logic4Vec value{};
  bool is_forced = false;
  Logic4Vec forced_value{};
  Logic4Vec pending_nba{};
  bool has_pending_nba = false;
};

}  // namespace delta
