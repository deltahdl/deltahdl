#pragma once

#include <cstdint>
#include <string>

#include "common/types.h"

using namespace delta;

// Decodes a packed 4-state value into the ASCII string it represents, taking
// the leftmost character from the high byte position (left bound to right
// bound) and skipping NUL bytes. Mirrors the byte-extraction loop used by the
// string-format system tasks (§21.3.3).
inline std::string Logic4VecToPackedString(const Logic4Vec& v) {
  std::string out;
  uint32_t nbytes = v.width / 8;
  for (uint32_t i = nbytes; i > 0; --i) {
    uint32_t byte_idx = i - 1;
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    if (word >= v.nwords) continue;
    auto ch = static_cast<char>((v.words[word].aval >> bit) & 0xFF);
    if (ch != 0) out += ch;
  }
  return out;
}
