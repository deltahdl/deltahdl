#pragma once

#include <cstdint>
#include <optional>
#include <string_view>

#include "lexer/token.h"

namespace delta {

enum class KeywordVersion : uint8_t {
  kVer13641995 = 0,
  kVer13642001 = 1,
  kVer13642001Noconfig = 2,
  kVer13642005 = 3,
  kVer18002005 = 4,
  kVer18002009 = 5,
  kVer18002012 = 6,
  kVer18002017 = 7,
  kVer18002023 = 8,
};

inline constexpr char kKeywordMarker = '\x01';

std::optional<KeywordVersion> ParseKeywordVersion(std::string_view spec);
std::optional<TokenKind> LookupKeyword(
    std::string_view text,
    KeywordVersion version = KeywordVersion::kVer18002023);

}  // namespace delta
