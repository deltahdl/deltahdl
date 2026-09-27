#include "simulator/contassign_delay.h"

#include <algorithm>
#include <cstdint>

#include "common/types.h"
#include "simulator/evaluation.h"

namespace delta {

static bool IsAllHighZ(const Logic4Vec& v) {
  for (uint32_t i = 0; i < v.nwords; ++i) {
    if (v.words[i].aval != 0 || v.words[i].bval == 0) return false;
  }
  return v.nwords > 0;
}

static uint64_t SelectScalarContAssignDelay(const Logic4Vec& old_val,
                                            const Logic4Vec& new_val,
                                            const ContAssignDelays& d) {
  bool new_has_x = HasUnknownBits(new_val);
  if (new_has_x) {
    uint64_t m = std::min(d.rise, d.fall);
    if (d.has_decay) m = std::min(m, d.decay);
    return m;
  }
  if (HasUnknownBits(old_val) || IsAllHighZ(old_val)) {
    // Old value is x or z, new value is a known 0 or 1. The destination
    // logic level selects the slot: 0 routes through the fall delay and 1
    // through the rise delay, matching the x/z-source rows of Table 28-9.
    return new_val.ToUint64() == 0 ? d.fall : d.rise;
  }
  uint64_t nv = new_val.ToUint64();
  uint64_t ov = old_val.ToUint64();
  if (nv > ov) return d.rise;
  if (nv < ov) return d.fall;
  return d.rise;
}

// §10.3.3 decides which of the three delays governs, and for a vector net it
// decides it once for the assignment rather than once per bit: "If the
// left-hand side references a vector net, then up to three delays can be
// applied. The following rules determine which delay controls the assignment:
// If the right-hand side makes a transition from nonzero to zero, then the
// falling delay shall be used. If the right-hand side makes a transition to z,
// then the turn-off delay shall be used. For all other cases, the rising delay
// shall be used." Each rule reads the right-hand side whole, so a vector whose
// bits move in opposite directions is neither a transition to zero nor one to
// z, and the rising delay carries every bit of it: the whole vector settles at
// one time, not each bit at its own.
//
// The clause's later sentence restricts the same thing again for one of the two
// forms -- "if the assignment is to a vector net, then the rising and falling
// delays shall not be applied to the individual bits if the assignment is
// included in the declaration" -- and grants nothing to the other. A net delay
// reaches here as the driver's own delay, ApplyNetDeclDelaysToDrivers
// (src/elaborator/elaborator_net_delay.cpp) having added it to whatever the
// driver wrote, and it is selected by these same rules. So both forms settle a
// vector whole, which is what #3372 asked to be decided and recorded.
//
// A scalar left-hand side is the other half of the clause: "If the left-hand
// references a scalar net, then the delay shall be treated in the same way as
// for gate delays", which is Table 28-9 and is what
// SelectScalarContAssignDelay above reads.
uint64_t SelectContAssignDelay(const Logic4Vec& old_val,
                               const Logic4Vec& new_val,
                               const ContAssignDelays& d, uint32_t width) {
  if (!d.has_fall) return d.rise;

  bool new_is_z = IsAllHighZ(new_val);
  if (new_is_z) {
    if (d.has_decay) return d.decay;
    return std::min(d.rise, d.fall);
  }

  if (width <= 1) {
    return SelectScalarContAssignDelay(old_val, new_val, d);
  }

  if (!HasUnknownBits(new_val) && new_val.ToUint64() == 0 &&
      !HasUnknownBits(old_val) && !IsAllHighZ(old_val) &&
      old_val.ToUint64() != 0) {
    return d.fall;
  }
  return d.rise;
}

}  // namespace delta
