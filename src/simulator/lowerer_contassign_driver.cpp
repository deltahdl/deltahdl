#include "simulator/lowerer_contassign_driver.h"

#include <cstddef>
#include <cstdint>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/evaluation.h"
#include "simulator/net.h"
#include "simulator/statement_assign.h"
#include "simulator/variable.h"

namespace delta {

Logic4Vec ContAssignDriverValue(const ContAssignDriver& drv,
                                const Logic4Vec& value, Arena& arena) {
  uint32_t net_width = drv.net->resolved->value.width;
  if (!drv.partial) return ResizeToWidth(value, net_width, arena);
  Logic4Vec out = MakeAllHighZ(arena, net_width);
  if (drv.width > 0) {
    Logic4Vec sized = ResizeToWidth(value, drv.src_lo + drv.width, arena);
    DepositBitField(out, drv.lo,
                    ExtractBitField(arena, sized, drv.src_lo, drv.width),
                    drv.width);
  }
  return out;
}

void ApplyContAssignToNet(const ContAssignDriver& drv,
                          const ContAssignDrivenValue& driven, Scheduler* sched,
                          Arena& arena) {
  auto value = ContAssignDriverValue(drv, driven.value, arena);
  if (drv.first) {
    drv.net->drivers.push_back(value);
    drv.net->driver_strengths.push_back(driven.strength);
  } else {
    drv.net->drivers[drv.driver_idx] = value;
    drv.net->driver_strengths[drv.driver_idx] = driven.strength;
  }
  size_t slot = drv.first ? drv.net->drivers.size() - 1 : drv.driver_idx;
  if (drv.net->driver_origins.size() <= slot)
    drv.net->driver_origins.resize(slot + 1);
  drv.net->driver_origins[slot] = drv.origin;
  if (drv.net->driver_ports.size() <= slot)
    drv.net->driver_ports.resize(slot + 1);
  drv.net->driver_ports[slot] = drv.source_port;
  drv.net->Resolve(arena, sched);
  for (std::size_t i = 0; i < drv.net->driver_listeners.size(); ++i) {
    drv.net->driver_listeners[i](slot);
  }
}

}  // namespace delta
