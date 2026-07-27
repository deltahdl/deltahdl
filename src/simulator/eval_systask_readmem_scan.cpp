#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <iterator>
#include <string>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "parser/ast.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/eval_systask_readmem_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

// §21.4: a number in the load file carries neither a length nor a base; the
// task name fixes the radix (binary for $readmemb, hexadecimal for $readmemh).
// The unknown value (x), the high-impedance value (z), and underscores may
// appear within a number, so the token is parsed into a 4-state element value
// rather than a plain integer. Underscores are discarded separators; x/z
// preserve their per-bit nature in the loaded word.
// §21.4: decodes one character of a memory-load number into its (aval, bval)
// pair. A digit fixes aval; x/z/? set the unknown/high-impedance pattern across
// the character's bit span (4 bits for hex, 1 for binary). Returns false when
// the character is not part of a number (any non-digit/x/z/? such as '_'), in
// which case the caller skips it; out-args are unchanged on a false return.
bool DecodeMemNumberChar(char c, bool is_hex, uint8_t& aval, uint8_t& bval) {
  aval = 0;
  bval = 0;
  if (c == 'x' || c == 'X') {
    aval = is_hex ? 0xF : 0x1;
    bval = aval;
    return true;
  }
  if (c == 'z' || c == 'Z' || c == '?') {
    bval = is_hex ? 0xF : 0x1;
    return true;
  }
  int digit = -1;
  if (c >= '0' && c <= '9') {
    digit = c - '0';
  } else if (c >= 'a' && c <= 'f') {
    digit = c - 'a' + 10;
  } else if (c >= 'A' && c <= 'F') {
    digit = c - 'A' + 10;
  }
  if (digit < 0) return false;
  aval = static_cast<uint8_t>(digit);
  return true;
}

Logic4Vec ParseMemNumber(Arena& arena, const std::string& tok, bool is_hex,
                         uint32_t width) {
  std::vector<std::pair<bool, bool>> bits;  // (aval, bval), least bit first
  int per_char = is_hex ? 4 : 1;
  for (auto it = tok.rbegin(); it != tok.rend(); ++it) {
    char c = *it;
    if (c == '_') continue;
    uint8_t aval = 0;
    uint8_t bval = 0;
    if (!DecodeMemNumberChar(c, is_hex, aval, bval)) continue;
    for (int b = 0; b < per_char; ++b) {
      bits.push_back({(aval >> b) & 1, (bval >> b) & 1});
    }
  }
  auto vec = MakeLogic4Vec(arena, width);
  for (uint32_t i = 0; i < width && i < bits.size(); ++i) {
    if (bits[i].first) vec.words[i / 64].aval |= uint64_t{1} << (i % 64);
    if (bits[i].second) vec.words[i / 64].bval |= uint64_t{1} << (i % 64);
  }
  return vec;
}

// §21.4.2: a 2-state destination — such as an int or bit vector, or an
// enumerated type with a 2-state base — cannot hold x or z, so any unknown or
// high-impedance bit read from the load file is turned into 0. In the 4-state
// encoding an x bit is aval=bval=1 and a z bit is aval=0/bval=1; clearing every
// bit whose bval is set and then dropping bval reduces both to a plain 0, while
// 0 and 1 bits are left unchanged. Reading otherwise proceeds exactly as for a
// 4-state element type.
void CoerceToTwoState(Logic4Vec& v) {
  for (uint32_t i = 0; i < v.nwords; ++i) {
    v.words[i].aval &= ~v.words[i].bval;
    v.words[i].bval = 0;
  }
}

// §21.4.2: file data for an enumerated destination is the numeric value of one
// of the type's elements (see 6.19). A number matching no element is out of
// range for the type.
bool EnumValueInRange(const EnumTypeInfo* info, const Logic4Vec& v) {
  uint64_t val = v.ToUint64();
  for (const auto& m : info->members) {
    if (m.value == val) return true;
  }
  return false;
}

// §21.4: walks a memory-load text file in file order. White space and both
// comment styles separate tokens. Each @-address (a hexadecimal index with no
// intervening white space) is handed to on_addr; each unsized number is handed
// to on_word (see ParseMemNumber for its grammar). Either callback returns
// false to abort the scan (an out-of-range address, for example).
// §21.4: true for the white space that separates load-file tokens.
bool IsMemFileSpace(char c) {
  return c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\f' ||
         c == '\v';
}

// §21.4: when `pos` sits at the start of a comment, advances it past the whole
// comment and returns true; otherwise leaves `pos` untouched and returns false.
// Both the // line form and the /* */ block form are recognized.
bool SkipMemFileComment(const std::string& content, size_t n, size_t& pos) {
  char c = content[pos];
  if (c == '/' && pos + 1 < n && content[pos + 1] == '/') {
    pos += 2;
    while (pos < n && content[pos] != '\n') ++pos;
    return true;
  }
  if (c == '/' && pos + 1 < n && content[pos + 1] == '*') {
    pos += 2;
    while (pos + 1 < n && (content[pos] != '*' || content[pos + 1] != '/')) {
      ++pos;
    }
    pos = (pos + 1 < n) ? pos + 2 : n;
    return true;
  }
  return false;
}

// §21.4: reads a token starting at `pos` — a maximal run of characters bounded
// by white space or the start of a comment — advancing `pos` past it.
std::string ScanMemFileToken(const std::string& content, size_t n,
                             size_t& pos) {
  size_t begin = pos;
  while (pos < n) {
    char t = content[pos];
    if (IsMemFileSpace(t)) break;
    if (t == '/' && pos + 1 < n &&
        (content[pos + 1] == '/' || content[pos + 1] == '*')) {
      break;
    }
    ++pos;
  }
  return content.substr(begin, pos - begin);
}

}  // namespace delta
