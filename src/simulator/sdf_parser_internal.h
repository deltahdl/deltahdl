#pragma once

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "simulator/sdf_parser.h"

namespace delta {

enum class SdfTokKind : uint8_t {
  kLParen,
  kRParen,
  kColon,
  kIdent,
  kString,
  kNumber,
  kEof,
};

struct SdfToken {
  SdfTokKind kind = SdfTokKind::kEof;
  std::string_view text;
  uint64_t num_val = 0;
  bool is_negative = false;
  double real_val = 0.0;
};

void SkipWhitespace(std::string_view& s);
SdfToken NextSdfToken(std::string_view& s);
bool Expect(std::string_view& s, SdfTokKind kind);
void SkipSdfParen(std::string_view& s);
SdfDelayValue ParseDelayVal(std::string_view& s);

std::vector<std::string> ParseSdfCondTokens(std::string_view& s);
std::string JoinSdfCondTokens(const std::vector<std::string>& tokens,
                              std::size_t count);

bool MapCheckType(std::string_view name, SdfCheckType& out);
SdfTimingCheck ParseOneTc(std::string_view& s, SdfCheckType type);

}  // namespace delta
