#pragma once

#include <string_view>
#include <vector>

#include "simulator/vpi_user.h"

namespace delta {

std::vector<s_vpi_vecval> VpiTableEntryVector(std::string_view row);

}  // namespace delta
