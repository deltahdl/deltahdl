#pragma once

#include <cstdint>

struct MinTypMax {
  uint64_t min_val = 0;
  uint64_t typ_val = 0;
  uint64_t max_val = 0;
};

enum class ChargeDecayState : uint8_t { kIdle, kDecaying, kDone };

inline uint64_t SelectMinTypMax(const MinTypMax& mtm, uint8_t selector) {
  switch (selector) {
    case 0:
      return mtm.min_val;
    case 1:
      return mtm.typ_val;
    case 2:
      return mtm.max_val;
    default:
      return mtm.typ_val;
  }
}
