#pragma once

#include <cstdint>

#include "common/arena.h"
#include "common/types.h"

using namespace delta;

inline Logic4Vec MakeZVec(Arena& arena, uint32_t width) {
  auto v = MakeLogic4Vec(arena, width);
  for (uint32_t w = 0; w < v.nwords; ++w) {
    v.words[w].aval = uint64_t{0};
    v.words[w].bval = ~uint64_t{0};
  }
  return v;
}

inline bool IsAllZ(const Logic4Vec& v) {
  for (uint32_t w = 0; w < v.nwords; ++w) {
    uint64_t mask = WordMaskWithinWidth(v.width, w);
    if ((v.words[w].aval & mask) != uint64_t{0}) return false;
    if ((v.words[w].bval & mask) != mask) return false;
  }
  return true;
}
