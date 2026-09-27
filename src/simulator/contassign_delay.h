#pragma once

// §10.3.3 and §28.16: which of a continuous assignment's rise, fall and
// turn-off delays carries one transition of its target. Split out of
// simulator/lowerer_contassign.cpp, which lowers the assignment and runs the
// process that waits these delays out, because that file reached the line
// limit assert-no-oversized-source-files holds sources to; the choice of delay
// reads the two values and the delays and nothing of the process.

#include <cstdint>

#include "common/types.h"

namespace delta {

// The delays an assignment's delay expressions evaluated to: `rise` always,
// `fall` and `decay` where the assignment wrote a second and a third.
struct ContAssignDelays {
  uint64_t rise = 0;
  uint64_t fall = 0;
  uint64_t decay = 0;
  bool has_fall = false;
  bool has_decay = false;
};

// The delay §10.3.3 gives the transition of a `width`-bit target from
// `old_val` to `new_val`: Table 28-9 for a scalar, the clause's three rules
// for a vector. Defined in simulator/contassign_delay.cpp.
uint64_t SelectContAssignDelay(const Logic4Vec& old_val,
                               const Logic4Vec& new_val,
                               const ContAssignDelays& d, uint32_t width);

}  // namespace delta
