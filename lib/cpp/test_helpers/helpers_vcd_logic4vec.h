#pragma once

#include <cstdint>
#include <cstring>

#include "common/arena.h"
#include "simulator/variable.h"

using namespace delta;

// Build a real-valued Logic4Vec holding the IEEE Std 754 bit pattern of d,
// mirroring how the evaluator stores a real result.
inline Logic4Vec MakeReal(Arena& arena, double d) {
  uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(double));
  Logic4Vec v = MakeLogic4VecVal(arena, 64, bits);
  v.is_real = true;
  return v;
}

// Build a 1-bit Logic4Vec from raw aval/bval bits so all four logic states can
// be exercised: (0,0)=0, (1,0)=1, (0,1)=x, (1,1)=z.
inline Logic4Vec MakeScalar(Arena& arena, uint64_t aval, uint64_t bval) {
  Logic4Vec v = MakeLogic4VecVal(arena, 1, aval);
  v.words[0].bval = bval;
  return v;
}
