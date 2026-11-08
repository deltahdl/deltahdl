#pragma once

#include <cstdint>
#include <optional>
#include <string_view>

#include "lexer/token.h"

namespace delta {

enum class KeywordVersion : uint8_t {
  kVer13641995 = 0x10,
  kVer13642001 = 0x11,
  kVer13642001Noconfig = 0x12,
  kVer13642005 = 0x13,
  kVer18002005 = 0x14,
  kVer18002009 = 0x15,
  kVer18002012 = 0x16,
  kVer18002017 = 0x17,
  kVer18002023 = 0x18,
};

inline constexpr char kKeywordMarker = '\x01';

std::optional<KeywordVersion> ParseKeywordVersion(std::string_view spec);
std::optional<TokenKind> LookupKeyword(
    std::string_view text,
    KeywordVersion version = KeywordVersion::kVer18002023);

}  // namespace delta
