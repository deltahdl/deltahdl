#pragma once

// §28.12.2 and §28.12.4: one bit of a net some driver of which drives x there.
//
// Such a driver is a signal of ambiguous strength: an L or an H -- an outcome
// that is 0 or z, or one that is 1 or z (§28.6 Table 28-5, §28.7 Table 28-6)
// -- or an x at a strength on each side (§28.12.2's signals whose value is x).
// The net takes every value and strength its drivers could give
// it together, so each such driver is taken as the states it stands for -- an
// L as 0 at its level or z, an H as 1 at its level or z, an x as 0 at its
// 0-side level or 1 at its 1-side level -- and the states the drivers can
// resolve to are gathered, the net's range running over all of them. That is
// §28.12.4's method of pairing every strength level of one signal with every
// level of the other and taking all the outcomes, and it reproduces §28.12.2's
// worked results: Figure 28-11's upper combination of an H and a pullup is 651
// and its lower one of an L and a weak 0 is 530, the two together are 56X
// (Figure 28-14), and Figure 28-16's strong H with a weak 0 is 36X (Figure
// 28-19). Applying §28.12.3's rules a) to c) to all the drivers at once instead
// drops an L at the pull level against a pullup, with which it conflicts, and
// fills rule c's gap below a range no weaker driver can reach, which the
// figures do not.

#include <cstdint>
#include <vector>

#include "common/types.h"
#include "simulator/net.h"

namespace delta {

// Whether some driver drives bit `bit` at x.
bool AnyDriverUnknownAt(const std::vector<Logic4Vec>& drivers, uint32_t bit);

// Resolves bit `bit` of a net of type `type` from its drivers as above,
// setting `out` to the range of strengths it can hold and answering its value:
// 0 or 1 where every state it can resolve to is that value, z where it can
// resolve to high impedance alone, and x otherwise (2 and 3 for x and z, as
// the net's bit helpers number them). Defined in
// simulator/net_bit_outcomes.cpp.
uint8_t ResolveBitOverDriverStates(const std::vector<Logic4Vec>& drivers,
                                   const std::vector<DriverStrength>& strengths,
                                   NetType type, uint32_t bit,
                                   NetStrength& out);

}  // namespace delta
