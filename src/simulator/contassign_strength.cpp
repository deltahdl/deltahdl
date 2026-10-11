#include "simulator/contassign_strength.h"

#include <cstdint>

#include "common/arena.h"
#include "common/types.h"
#include "simulator/net.h"

namespace delta {

Strength StrengthFromParserCode(uint8_t s) {
  switch (s) {
    case 1:
      return Strength::kHighz;
    case 2:
      return Strength::kWeak;
    case 3:
      return Strength::kPull;
    case 4:
      return Strength::kStrong;
    case 5:
      return Strength::kSupply;
    default:
      return Strength::kStrong;
  }
}

Logic4Vec ApplyHighzStrengthsToValue(const Logic4Vec& val, DriverStrength ds,
                                     Arena& arena) {
  bool s0_is_z = (ds.s0 == Strength::kHighz);
  bool s1_is_z = (ds.s1 == Strength::kHighz);
  if (!s0_is_z && !s1_is_z) return val;
  auto out = MakeLogic4Vec(arena, val.width);
  out.is_real = val.is_real;
  out.is_signed = val.is_signed;
  out.is_string = val.is_string;
  for (uint32_t w = 0; w < val.nwords; ++w) {
    uint64_t a = val.words[w].aval;
    uint64_t b = val.words[w].bval;
    uint64_t mask = ~uint64_t{0};
    uint32_t bits_done = w * 64;
    if (val.width > bits_done && val.width - bits_done < 64)
      mask = (uint64_t{1} << (val.width - bits_done)) - 1;
    uint64_t to_z = 0;
    if (s0_is_z) to_z |= (~a & ~b) & mask;
    if (s1_is_z) to_z |= (a & ~b) & mask;
    // A high-impedance bit is z = (aval=0, bval=1).
    out.words[w].aval = a & ~to_z;
    out.words[w].bval = b | to_z;
  }
  return out;
}

}  // namespace delta
