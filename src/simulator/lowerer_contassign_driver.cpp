#include "simulator/lowerer_contassign_driver.h"

#include <cstddef>
#include <cstdint>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/evaluation.h"
#include "simulator/net.h"
#include "simulator/statement_assign.h"

namespace delta {

// The value this assignment contributes to its net's resolution, over the
// net's full width.
//
// §10.7: the left-hand side's size is the context the right-hand expression is
// sized in, and a right-hand side of fewer bits is padded out to that size,
// sign-extended where it is signed. For a bare identifier the left-hand side is
// the net, so the value is extended to it -- pushed as it stands it would drive
// the low bits and leave every bit above them to resolve as undriven.
//
// For a select the left-hand side is the selected bits, so the padding context
// is their width, and the driver is that value in place with high impedance
// around it. §28.12 then resolves each bit against the net's other sources, and
// the bits this assignment does not name are decided without it -- which is
// what a source driving part of a net is.
//
// A select running off the low end of the net does not land the value's low
// bits: §11.5.1 gives the bits that are in range the value's bits at and above
// `src_lo`. The padding context is then `src_lo + drv.width`, the number of the
// select's own bits at and below the ones that land, and the deposit takes its
// source from `src_lo`. The select's bits above those are discarded either way.
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
  // ApplyContAssignToNet is the net's half of the same step
  // ApplyContAssignToVariable takes for a variable target.
  auto value = ContAssignDriverValue(drv, driven.value, arena);
  if (drv.first) {
    drv.net->drivers.push_back(value);
    drv.net->driver_strengths.push_back(driven.strength);
  } else {
    drv.net->drivers[drv.driver_idx] = value;
    drv.net->driver_strengths[drv.driver_idx] = driven.strength;
  }
  // §21.7.4.3.2: which instance this driver stands in, kept slot for slot.
  size_t slot = drv.first ? drv.net->drivers.size() - 1 : drv.driver_idx;
  if (drv.net->driver_origins.size() <= slot)
    drv.net->driver_origins.resize(slot + 1);
  drv.net->driver_origins[slot] = drv.origin;
  // §28.16.2.1: when this update leaves a trireg net with only high-impedance
  // drivers it enters the charge storage state, and Resolve arms the charge
  // decay process by scheduling the transition to x on the scheduler. Pass the
  // scheduler through so a driver turning off actually starts that process at
  // run time (a null scheduler would silently drop it).
  drv.net->Resolve(arena, sched);
}

}  // namespace delta
