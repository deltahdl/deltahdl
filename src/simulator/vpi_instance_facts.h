#pragma once

#include <cstdint>
#include <vector>

#include "simulator/vpi_user.h"

namespace delta {

struct VpiObject;

struct VpiInstanceFacts {
  bool cell = false;
  bool protected_definition = false;
  int default_net_type = vpiWire;
  int unconnected_drive = vpiHighZ;
  int delay_mode = vpiDelayModeNone;
  std::vector<int64_t> array_indices;
  mutable std::vector<VpiObject*> imported;
};

}  // namespace delta
