#pragma once

// §10.3: the driver slot one continuous assignment holds on the net it drives,
// and the step that writes the assignment's value into that slot and resolves
// the net. Shared by the continuous-assignment process (lowerer_contassign.cpp)
// and kept apart from it so that file stays within the source-size gate.

#include <cstddef>
#include <cstdint>
#include <string_view>

#include "common/types.h"
#include "simulator/net.h"

namespace delta {

class Arena;
class Scheduler;

// Identifies the driver slot that a continuous assignment writes to. Per IEEE
// 1800 §10.3, a continuous assignment drives a single net (or variable) through
// one driver; `net` is the resolved net (null when the target is a variable),
// `driver_idx` is that driver's slot within the net, and `first` is true on the
// initial commit, when the driver slot must be appended rather than
// overwritten.
struct ContAssignDriver {
  Net* net = nullptr;
  size_t driver_idx = 0;
  bool first = true;
  // §10.3.2: which bits of `net` this assignment drives. A bare identifier
  // drives the whole net; a select drives the bits §11.5.1 gives its indices
  // and high impedance everywhere else, so that §28.12 combines it with the
  // net's other sources the way it combines any two. `lo` counts from the least
  // significant end of the net's storage, and a width of zero with `partial`
  // set is the select that addresses no bit of the net at all -- an index out
  // of range, or one carrying x or z -- which §11.5.1 gives no effect and which
  // therefore drives nothing.
  bool partial = false;
  uint32_t lo = 0;
  uint32_t width = 0;
  // §11.5.1's second answer for a select that is only partly in range: a
  // partially out-of-range part-select, when written, changes only the bits
  // that are in range, which names both the bits of the net that are
  // written -- `lo` and `width` -- and the bits of the value those bits take.
  // `src_lo` is where in the value they begin: it counts the select's own low
  // bits that fall below the net, so it is zero for a select wholly inside the
  // net and for one running off the high end, whose landing bits are the
  // value's least significant ones, and positive for one running off the low
  // end. §11.5.1 reads `a[1 -: 4]` on a `tri0 [7:0] a` as `a[1:-2]`, whose most
  // significant end is index 1, so `a[1]` takes the value's bit 3 and `a[0]`
  // its bit 2 and `assign a[1 -: 4] = 4'b1101` must leave `a` at 8'h03; driving
  // the value's low two bits left it at 8'h01.
  uint32_t src_lo = 0;
  // §21.7.4.3.2: the instance the assignment stands in, its hierarchical prefix
  // (`k1.`, or empty for the top), recorded on the net beside the driver
  // (Net::driver_origins) so a dumped inout port can tell the drivers inside
  // its instance from those outside it.
  std::string_view origin;
  // §32.4.4: the module output port this assignment carries out of its
  // instance, where it is that port's connection (Net::driver_ports).
  std::string_view source_port;
};

// The value a continuous-assignment driver contributes to net resolution: the
// driven logic value paired with the driver strength selected for it (IEEE 1800
// §10.3, §28.x driver strengths).
struct ContAssignDrivenValue {
  const Logic4Vec& value;
  DriverStrength strength;
};

// The value the driver `drv` contributes to its net's resolution, over the
// net's full width (§10.7, §11.5.1).
Logic4Vec ContAssignDriverValue(const ContAssignDriver& drv,
                                const Logic4Vec& value, Arena& arena);
// Writes `driven` into the driver's slot on its net, appending the slot on the
// first commit, and resolves the net (§28.12, §28.16.2.1).
void ApplyContAssignToNet(const ContAssignDriver& drv,
                          const ContAssignDrivenValue& driven, Scheduler* sched,
                          Arena& arena);

}  // namespace delta
