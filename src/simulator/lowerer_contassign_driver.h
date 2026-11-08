#pragma once

#include <cstddef>
#include <cstdint>
#include <string_view>

#include "common/types.h"
#include "simulator/net.h"

namespace delta {

class Arena;
class Scheduler;

struct ContAssignDriver {
  Net* net = nullptr;
  size_t driver_idx = 0;
  bool first = true;
  bool partial = false;
  uint32_t lo = 0;
  uint32_t width = 0;
  uint32_t src_lo = 0;
  std::string_view origin;
  std::string_view source_port;
};

struct ContAssignDrivenValue {
  const Logic4Vec& value;
  DriverStrength strength;
};

Logic4Vec ContAssignDriverValue(const ContAssignDriver& drv,
                                const Logic4Vec& value, Arena& arena);
void ApplyContAssignToNet(const ContAssignDriver& drv,
                          const ContAssignDrivenValue& driven, Scheduler* sched,
                          Arena& arena);

}  // namespace delta
