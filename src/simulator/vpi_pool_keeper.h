#pragma once

#include <deque>
#include <string>

#include "simulator/vpi_design_attach_build.h"

namespace delta {

// What keeps a name in `pool`, answering the kept copy, which lives as long
// as `pool` does: the keeper of the names VpiContext gives its objects.
VpiNameKeeper VpiPoolKeeper(std::deque<std::string>& pool);

}  // namespace delta
