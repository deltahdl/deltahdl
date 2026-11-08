#pragma once

#include <deque>
#include <string>

#include "simulator/vpi_design_attach_build.h"

namespace delta {

VpiNameKeeper VpiPoolKeeper(std::deque<std::string>& pool);

}  // namespace delta
