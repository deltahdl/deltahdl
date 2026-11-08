#include "simulator/vpi_value_strings.h"

#include <algorithm>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "common/types.h"
#include "simulator/eval_format_internal.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

uint8_t GroupBits(const Logic4Vec& v, bool bval, int lo, int count) {
  uint8_t bits = 0;
  for (int k = 0; k < count; ++k) {
    const Logic4Word& word = v.words[(lo + k) / 64];
    const uint64_t kHeld = bval ? word.bval : word.aval;
    bits |= static_cast<uint8_t>(((kHeld >> ((lo + k) % 64)) & 1) << k);
  }
  return bits;
}

char HexDigitFromBits(uint8_t nibble) {
  if (nibble < 10) return static_cast<char>('0' + nibble);
  return static_cast<char>('a' + nibble - 10);
}

char UnknownGroupChar(uint8_t a_bits, uint8_t b_bits, uint8_t mask) {
  uint8_t unknown = b_bits & mask;
  uint8_t x_bits = a_bits & b_bits & mask;
  if (x_bits != 0) {
    bool all_x = unknown == mask && (a_bits & mask) == mask;
    return all_x ? 'x' : 'X';
  }
  bool all_z = unknown == mask;
  return all_z ? 'z' : 'Z';
}

}  // namespace

void GetValueBinStr(const Logic4Vec& v, s_vpi_value* value,
                    std::vector<std::string>& pool) {
  int width = static_cast<int>(v.width);
  std::string result;
  result.reserve(width);
  for (int i = width - 1; i >= 0; --i) {
    bool a_bit = GroupBits(v, false, i, 1) != 0;
    bool b_bit = GroupBits(v, true, i, 1) != 0;
    if (!b_bit) {
      result += (a_bit ? '1' : '0');
    } else {
      result += (a_bit ? 'x' : 'z');
    }
  }
  pool.push_back(std::move(result));
  value->value.str = VpiText(pool.back().c_str());
}

void GetValueHexStr(const Logic4Vec& v, s_vpi_value* value,
                    std::vector<std::string>& pool) {
  int width = static_cast<int>(v.width);
  int hex_digits = (width + 3) / 4;
  std::string result;
  result.reserve(hex_digits);
  for (int i = hex_digits - 1; i >= 0; --i) {
    int valid = std::min(4, width - i * 4);
    uint8_t a_nibble = GroupBits(v, false, i * 4, valid);
    uint8_t b_nibble = GroupBits(v, true, i * 4, valid);
    if (b_nibble != 0) {
      result += UnknownGroupChar(a_nibble, b_nibble,
                                 static_cast<uint8_t>((1u << valid) - 1));
    } else {
      result += HexDigitFromBits(a_nibble);
    }
  }
  pool.push_back(std::move(result));
  value->value.str = VpiText(pool.back().c_str());
}

void GetValueOctStr(const Logic4Vec& v, s_vpi_value* value,
                    std::vector<std::string>& pool) {
  int width = static_cast<int>(v.width);
  int oct_digits = (width + 2) / 3;
  std::string result;
  result.reserve(oct_digits);
  for (int i = oct_digits - 1; i >= 0; --i) {
    int valid = std::min(3, width - i * 3);
    uint8_t a_bits = GroupBits(v, false, i * 3, valid);
    uint8_t b_bits = GroupBits(v, true, i * 3, valid);
    if (b_bits != 0) {
      result += UnknownGroupChar(a_bits, b_bits,
                                 static_cast<uint8_t>((1u << valid) - 1));
    } else {
      result += static_cast<char>('0' + a_bits);
    }
  }
  pool.push_back(std::move(result));
  value->value.str = VpiText(pool.back().c_str());
}

void GetValueStringVal(const Logic4Vec& v, s_vpi_value* value,
                       std::vector<std::string>& pool) {
  const int kWidth = static_cast<int>(v.width);
  std::string s;
  for (int byte = (kWidth + 7) / 8 - 1; byte >= 0; --byte) {
    const int kBits = std::min(8, kWidth - byte * 8);
    auto ch = static_cast<char>(GroupBits(v, false, byte * 8, kBits) &
                                ~GroupBits(v, true, byte * 8, kBits));
    if (ch != 0) s += ch;
  }
  pool.push_back(std::move(s));
  value->value.str = VpiText(pool.back().c_str());
}

void GetValueDecStr(const Logic4Vec& v, s_vpi_value* value,
                    std::vector<std::string>& pool) {
  std::vector<Logic4Word> known(v.words, v.words + v.nwords);
  for (Logic4Word& word : known) {
    word.aval &= ~word.bval;
    word.bval = 0;
  }
  Logic4Vec digits = v;
  digits.words = known.data();
  pool.push_back(FormatDecimalDigits(digits));
  value->value.str = VpiText(pool.back().c_str());
}

}  // namespace delta
