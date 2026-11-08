#include <algorithm>
#include <cctype>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <iterator>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/eval_systask_readmem_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"

namespace delta {

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
  std::vector<std::pair<bool, bool>> bits;
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

void CoerceToTwoState(Logic4Vec& v) {
  for (uint32_t i = 0; i < v.nwords; ++i) {
    v.words[i].aval &= ~v.words[i].bval;
    v.words[i].bval = 0;
  }
}

bool EnumValueInRange(const EnumTypeInfo* info, const Logic4Vec& v) {
  uint64_t val = v.ToUint64();
  for (const auto& m : info->members) {
    if (m.value == val) return true;
  }
  return false;
}

bool IsMemFileSpace(char c) {
  return c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\f' ||
         c == '\v';
}

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

static bool IsMemNumberChar(char c, bool is_hex) {
  if (c == 'x' || c == 'X' || c == 'z' || c == 'Z' || c == '?' || c == '_')
    return true;
  if (is_hex) return std::isxdigit(static_cast<unsigned char>(c)) != 0;
  return c == '0' || c == '1';
}

bool CheckMemFileToken(const ReadmemEnv& env, const std::string& tok) {
  std::string task = std::string("$readmem") + (env.is_hex ? "h" : "b");
  if (tok[0] == '@') {
    std::string_view digits = std::string_view(tok).substr(1);
    if (!digits.empty() && std::ranges::all_of(digits, [](char c) {
          return std::isxdigit(static_cast<unsigned char>(c)) != 0;
        }))
      return true;
    env.ctx.GetDiag().Error(
        env.loc,
        task + ": '" + tok +
            "': '@' is not followed directly by a hexadecimal address",
        Subclause("21.4"));
    return false;
  }
  if (std::ranges::all_of(
          tok, [&](char c) { return IsMemNumberChar(c, env.is_hex); }))
    return true;
  env.ctx.GetDiag().Error(env.loc,
                          task + ": '" + tok + "' is not an unsized " +
                              (env.is_hex ? "hexadecimal" : "binary") +
                              " number",
                          Subclause("21.4"));
  return false;
}

}  // namespace delta
