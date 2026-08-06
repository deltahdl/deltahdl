#pragma once

#include <cstdint>

#include "common/arena.h"
#include "simulator/variable.h"

using namespace delta;

// Build a 1-bit Logic4Vec from raw aval/bval bits so all four logic states can
// be exercised: (0,0)=0, (1,0)=1, (0,1)=x, (1,1)=z.
inline Logic4Vec MakeScalar(Arena& arena, uint64_t aval, uint64_t bval) {
  Logic4Vec v = MakeLogic4VecVal(arena, 1, aval);
  v.words[0].bval = bval;
  return v;
}
