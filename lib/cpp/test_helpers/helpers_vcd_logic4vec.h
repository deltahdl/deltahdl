#pragma once

#include <cstdint>

#include "common/arena.h"
#include "common/types.h"

using namespace delta;

inline Logic4Vec MakeScalar(Arena& arena, uint64_t aval, uint64_t bval) {
  Logic4Vec v = MakeLogic4VecVal(arena, 1, aval);
  v.words[0].bval = bval;
  return v;
}
