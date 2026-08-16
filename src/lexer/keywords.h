#pragma once

#include <cstdint>
#include <optional>
#include <string_view>

#include "lexer/token.h"

namespace delta {

// The version_specifier a `begin_keywords directive selects (Syntax 22-10),
// ordered oldest first: LookupKeyword compares a keyword's earliest version
// against the one in force, so the relative order carries meaning and the
// absolute values do not.
//
// The values start above kKeywordMarker so that none of them equals it. The
// Preprocessor writes a marker and a version as two adjacent bytes, so an
// enumerator equal to the marker makes the second byte of one region read as
// the start of another to anything scanning the text for markers rather than
// walking it from the beginning. Staying below 0x80 keeps the byte positive in
// a signed char, which is what Lexer::ConsumeKeywordMarker casts back.
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

// Introduces the version byte the Preprocessor writes where a `begin_keywords
// or `end_keywords directive stood. A source file may not contain this byte:
// Preprocessor::ProcessSource reports every one it reads under §5.2 and blanks
// it, so that each marker in preprocessed text is one the Preprocessor wrote.
inline constexpr char kKeywordMarker = '\x01';

std::optional<KeywordVersion> ParseKeywordVersion(std::string_view spec);
std::optional<TokenKind> LookupKeyword(
    std::string_view text,
    KeywordVersion version = KeywordVersion::kVer18002023);

}  // namespace delta
