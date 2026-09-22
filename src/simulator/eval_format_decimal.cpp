#include <cmath>
#include <cstdint>
#include <string>
#include <vector>

#include "common/types.h"
#include "simulator/eval_format_internal.h"

namespace delta {

namespace {

// The magnitude of `val` as 32-bit limbs, least significant first, the bits
// above the width cleared, and negated in two's complement within the width
// where `negative`, so that the limbs hold the magnitude of a signed value
// whose top bit is set.
std::vector<uint32_t> MagnitudeLimbs(const Logic4Vec& val, bool negative) {
  std::vector<uint32_t> limbs;
  uint32_t width = val.width == 0 ? 1 : val.width;
  uint32_t n_limbs = (width + 31) / 32;
  limbs.reserve(n_limbs);
  for (uint32_t i = 0; i < n_limbs; ++i) {
    uint32_t word = i / 2;
    uint64_t aval = word < val.nwords ? val.words[word].aval : 0;
    auto limb = static_cast<uint32_t>(aval >> ((i % 2) * 32));
    uint32_t valid = width - i * 32;
    if (valid < 32) limb &= (uint32_t{1} << valid) - 1;
    limbs.push_back(limb);
  }
  if (!negative) return limbs;
  uint64_t carry = 1;
  for (uint32_t i = 0; i < n_limbs; ++i) {
    uint32_t valid = width - i * 32;
    uint32_t mask = valid < 32 ? (uint32_t{1} << valid) - 1 : 0xFFFFFFFFu;
    uint64_t sum = static_cast<uint64_t>(~limbs[i] & mask) + carry;
    limbs[i] = static_cast<uint32_t>(sum) & mask;
    carry = sum >> 32;
  }
  return limbs;
}

constexpr uint32_t kChunkBase = 1000000000u;
constexpr uint32_t kChunkDigits = 9;

// Divides the limbs in place by 10^9 and returns the remainder; the limbs
// read zero once the quotient is.
uint32_t DivideLimbsByChunkBase(std::vector<uint32_t>& limbs) {
  uint64_t rem = 0;
  for (auto it = limbs.rbegin(); it != limbs.rend(); ++it) {
    uint64_t cur = (rem << 32) | *it;
    *it = static_cast<uint32_t>(cur / kChunkBase);
    rem = cur % kChunkBase;
  }
  return static_cast<uint32_t>(rem);
}

bool LimbsAreZero(const std::vector<uint32_t>& limbs) {
  for (uint32_t limb : limbs) {
    if (limb != 0) return false;
  }
  return true;
}

}  // namespace

// §21.2.1.1: a decimal renders the whole value, whatever its width, where
// reading it through a 64-bit word rendered the low 64 bits alone -- the
// suite's 11.4.14.3--unpack_stream-sim.sv displayed its 96-bit
// 96'h00000003_00000002_00000001 as 8589934593 (#4363). The numeral is built
// nine digits at a time by long division of the magnitude's 32-bit limbs by
// 10^9, each remainder a chunk of the numeral from the right.
std::string FormatDecimalDigits(const Logic4Vec& val) {
  uint32_t width = val.width == 0 ? 1 : val.width;
  uint32_t top = width - 1;
  bool negative = val.is_signed && top / 64 < val.nwords &&
                  ((val.words[top / 64].aval >> (top % 64)) & 1u) != 0;
  std::vector<uint32_t> limbs = MagnitudeLimbs(val, negative);
  std::string digits;
  while (!LimbsAreZero(limbs)) {
    uint32_t chunk = DivideLimbsByChunkBase(limbs);
    std::string part = std::to_string(chunk);
    if (!LimbsAreZero(limbs)) {
      part.insert(0, kChunkDigits - part.size(), '0');
    }
    digits.insert(0, part);
  }
  if (digits.empty()) digits = "0";
  return negative ? "-" + digits : digits;
}

// §21.2.1.2: enough characters for the largest value the expression could
// possibly hold. An unsigned width-w value tops out at 2^w - 1, whose digit
// count is that of 2^w since no power of two is a power of ten; a signed one
// is bounded in print length by its most negative value, whose magnitude
// 2^(w-1) is joined by a sign column. The count is exact for a width the
// 64-bit loop can hold and is read off the base-10 logarithm above it, where
// a value sized as a 64-bit one gave a 96-bit field 20 columns instead of 29.
uint32_t AutoDecimalFieldWidth(const Logic4Vec& val) {
  uint32_t bits = val.width;
  if (bits == 0) bits = 1;
  uint32_t mag_bits = val.is_signed ? bits - 1 : bits;
  uint32_t digits = 1;
  if (mag_bits >= 64) {
    digits = static_cast<uint32_t>(std::floor(mag_bits * std::log10(2.0))) + 1;
  } else if (mag_bits > 0) {
    uint64_t max_mag =
        val.is_signed ? uint64_t{1} << mag_bits : (uint64_t{1} << mag_bits) - 1;
    while (max_mag >= 10) {
      max_mag /= 10;
      ++digits;
    }
  }
  return digits + (val.is_signed ? 1u : 0u);
}

}  // namespace delta
