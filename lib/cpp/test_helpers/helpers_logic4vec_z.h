#pragma once

#include <cstdint>

#include "common/arena.h"
#include "fixture_simulator.h"

using namespace delta;

// Builds a Logic4Vec of the given width with every bit set to the
// high-impedance (z) value. Canonical Convention A: z = (aval=0, bval=1).
inline Logic4Vec MakeZVec(Arena& arena, uint32_t width) {
  auto v = MakeLogic4Vec(arena, width);
  for (uint32_t w = 0; w < v.nwords; ++w) {
    v.words[w].aval = uint64_t{0};
    v.words[w].bval = ~uint64_t{0};
  }
  return v;
}

// Returns true when every word of the vector holds the high-impedance (z)
// value. Canonical Convention A: z = (aval=0, bval=1).
inline bool IsAllZ(const Logic4Vec& v) {
  for (uint32_t w = 0; w < v.nwords; ++w) {
    if (v.words[w].aval != uint64_t{0}) return false;
    if (v.words[w].bval != ~uint64_t{0}) return false;
  }
  return true;
}
