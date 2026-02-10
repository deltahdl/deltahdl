#pragma once

#include <cstdint>
#include <optional>
#include <string_view>

#include "lexer/token.h"

namespace delta {

// IEEE 1800-2023 §22.14 version specifiers, ordered so that for all versions
// except k1364_2001_noconfig, min_version <= active_version is the correct
// keyword membership test.  k1364_2001_noconfig slots between k1364_2001 and
// k1364_2005 and is handled as a special case in LookupKeyword.
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

// Sentinel byte that begins a keyword-version marker in preprocessed output.
// Format: kKeywordMarker + static_cast<char>(KeywordVersion) + '\n'.
inline constexpr char kKeywordMarker = '\x01';

std::optional<KeywordVersion> ParseKeywordVersion(std::string_view spec);
std::optional<TokenKind> LookupKeyword(
    std::string_view text,
    KeywordVersion version = KeywordVersion::kVer18002023);

}  // namespace delta
