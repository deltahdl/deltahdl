#include "preprocessor/protect_encoding_codecs.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

namespace delta {
namespace {

constexpr std::string_view kBase64Alphabet =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

constexpr std::string_view kBlockAlphabet =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_";

constexpr char kBase64Pad = '=';
constexpr char kNoPad = '\0';

std::string EncodeSixBitGroups(std::string_view bytes,
                               std::string_view alphabet, char pad) {
  std::string encoded;
  encoded.reserve(((bytes.size() + 2) / 3) * 4);
  for (size_t i = 0; i < bytes.size(); i += 3) {
    size_t have = std::min<size_t>(3, bytes.size() - i);
    uint32_t group = 0;
    for (size_t n = 0; n < have; ++n) {
      auto byte = static_cast<uint32_t>(static_cast<uint8_t>(bytes[i + n]));
      group |= byte << ((2 - n) * 8);
    }
    for (size_t n = 0; n <= have; ++n) {
      encoded.push_back(alphabet[(group >> ((3 - n) * 6)) & 0x3FU]);
    }
    if (pad == kNoPad) continue;
    for (size_t n = have; n < 3; ++n) encoded.push_back(pad);
  }
  return encoded;
}

bool AppendDecodedTail(uint32_t group, size_t have, std::string* bytes) {
  if (have == 0) return true;
  if (have == 1) return false;
  size_t leftover = 8 - (2 * have);
  for (size_t n = 0; n + 1 < have; ++n) {
    size_t shift = leftover + ((have - 2 - n) * 8);
    bytes->push_back(static_cast<char>((group >> shift) & 0xFFU));
  }
  return true;
}

bool DecodeSixBitGroups(std::string_view text, std::string_view alphabet,
                        std::string* bytes) {
  std::string decoded;
  uint32_t group = 0;
  size_t have = 0;
  for (char c : text) {
    size_t index = alphabet.find(c);
    if (index == std::string_view::npos) return false;
    group = (group << 6) | static_cast<uint32_t>(index);
    ++have;
    if (have < 4) continue;
    for (size_t n = 0; n < 3; ++n) {
      decoded.push_back(static_cast<char>((group >> ((2 - n) * 8)) & 0xFFU));
    }
    group = 0;
    have = 0;
  }
  if (!AppendDecodedTail(group, have, &decoded)) return false;
  bytes->assign(decoded);
  return true;
}

constexpr size_t kUuencodeMaxLineBytes = 45;

char UuencodeChar(size_t value) {
  if (value == 0) return '`';
  return static_cast<char>(value + 0x20U);
}

bool UuencodeValueOf(char c, size_t* value) {
  auto byte = static_cast<unsigned char>(c);
  if (byte < 0x20U || byte > 0x60U) return false;
  *value = static_cast<size_t>((byte - 0x20U) & 0x3FU);
  return true;
}

void AppendUuencodeGroups(std::string_view data, std::string* text) {
  for (size_t i = 0; i < data.size(); i += 3) {
    uint32_t group = 0;
    for (size_t n = 0; n < 3; ++n) {
      uint32_t byte =
          i + n < data.size()
              ? static_cast<uint32_t>(static_cast<uint8_t>(data[i + n]))
              : 0U;
      group |= byte << ((2 - n) * 8);
    }
    for (size_t n = 0; n < 4; ++n) {
      text->push_back(UuencodeChar((group >> ((3 - n) * 6)) & 0x3FU));
    }
  }
}

size_t UuencodeBytesPerLine(size_t line_length) {
  if (line_length == 0) return kUuencodeMaxLineBytes;
  size_t groups = line_length < 5 ? 1 : (line_length - 1) / 4;
  return std::min(groups * 3, kUuencodeMaxLineBytes);
}

bool AppendUuencodeLine(std::string_view line, size_t want,
                        std::string* bytes) {
  size_t taken = 0;
  size_t i = 0;
  while (taken < want) {
    if (i + 4 > line.size()) return false;
    uint32_t group = 0;
    for (size_t n = 0; n < 4; ++n) {
      size_t value = 0;
      if (!UuencodeValueOf(line[i + n], &value)) return false;
      group = (group << 6) | static_cast<uint32_t>(value);
    }
    i += 4;
    for (size_t n = 0; n < 3 && taken < want; ++n) {
      bytes->push_back(static_cast<char>((group >> ((2 - n) * 8)) & 0xFFU));
      ++taken;
    }
  }
  return true;
}

std::string_view NextLine(std::string_view text, size_t* pos) {
  size_t eol = text.find('\n', *pos);
  size_t end = eol == std::string_view::npos ? text.size() : eol;
  std::string_view line = text.substr(*pos, end - *pos);
  *pos = eol == std::string_view::npos ? text.size() : eol + 1;
  if (!line.empty() && line.back() == '\r') line.remove_suffix(1);
  return line;
}

constexpr size_t kQuotedPrintableMaxLine = 76;

constexpr size_t kQuotedPrintableMinLine = 4;

constexpr std::string_view kHexDigits = "0123456789ABCDEF";
constexpr std::string_view kLowerHexDigits = "0123456789abcdef";

bool IsQuotedPrintableLiteral(char c) {
  auto byte = static_cast<unsigned char>(c);
  if (byte >= 33U && byte <= 60U) return true;
  return byte >= 62U && byte <= 126U;
}

void AppendQuotedPrintableByte(char c, std::string* text) {
  if (IsQuotedPrintableLiteral(c)) {
    text->push_back(c);
    return;
  }
  auto byte = static_cast<unsigned char>(c);
  text->push_back('=');
  text->push_back(kHexDigits[(byte >> 4U) & 0x0FU]);
  text->push_back(kHexDigits[byte & 0x0FU]);
}

bool HexValueOf(char c, size_t* value) {
  size_t index = kHexDigits.find(c);
  if (index == std::string_view::npos) index = kLowerHexDigits.find(c);
  if (index == std::string_view::npos) return false;
  *value = index;
  return true;
}

bool AppendQuotedPrintableEscape(std::string_view text, size_t* i,
                                 std::string* decoded) {
  size_t at = *i + 1;
  if (at < text.size() && text[at] == '\r') ++at;
  if (at < text.size() && text[at] == '\n') {
    *i = at + 1;
    return true;
  }
  if (at + 1 >= text.size()) return false;
  size_t high = 0;
  size_t low = 0;
  if (!HexValueOf(text[at], &high)) return false;
  if (!HexValueOf(text[at + 1], &low)) return false;
  decoded->push_back(static_cast<char>((high << 4U) | low));
  *i = at + 2;
  return true;
}

}  // namespace

std::string EncodeBase64(std::string_view bytes) {
  return EncodeSixBitGroups(bytes, kBase64Alphabet, kBase64Pad);
}

bool DecodeBase64(std::string_view text, std::string* bytes) {
  std::string kept;
  kept.reserve(text.size());
  for (char c : text) {
    if (c == kBase64Pad) break;
    if (kBase64Alphabet.find(c) != std::string_view::npos) kept.push_back(c);
  }
  return DecodeSixBitGroups(kept, kBase64Alphabet, bytes);
}

std::string EncodeProtectBlockAlphabet(std::string_view bytes) {
  return EncodeSixBitGroups(bytes, kBlockAlphabet, kNoPad);
}

bool DecodeProtectBlockAlphabet(std::string_view text, std::string* bytes) {
  return DecodeSixBitGroups(text, kBlockAlphabet, bytes);
}

std::string EncodeUuencode(std::string_view bytes, size_t line_length) {
  size_t per_line = UuencodeBytesPerLine(line_length);
  std::string text;
  for (size_t i = 0; i < bytes.size(); i += per_line) {
    size_t have = std::min(per_line, bytes.size() - i);
    text.push_back(UuencodeChar(have));
    AppendUuencodeGroups(bytes.substr(i, have), &text);
    text.push_back('\n');
  }
  text.push_back(UuencodeChar(0));
  text.push_back('\n');
  return text;
}

bool DecodeUuencode(std::string_view text, std::string* bytes) {
  std::string decoded;
  size_t pos = 0;
  while (pos < text.size()) {
    std::string_view line = NextLine(text, &pos);
    if (line.empty()) continue;
    size_t want = 0;
    if (!UuencodeValueOf(line.front(), &want)) return false;
    if (want == 0) break;
    if (!AppendUuencodeLine(line.substr(1), want, &decoded)) return false;
  }
  bytes->assign(decoded);
  return true;
}

std::string EncodeQuotedPrintable(std::string_view bytes, size_t line_length) {
  size_t limit = line_length == 0 ? kQuotedPrintableMaxLine : line_length;
  limit = std::max(limit, kQuotedPrintableMinLine);
  std::string text;
  size_t column = 0;
  for (char c : bytes) {
    size_t width = IsQuotedPrintableLiteral(c) ? 1 : 3;
    if (column + width + 1 > limit) {
      text.append("=\n");
      column = 0;
    }
    AppendQuotedPrintableByte(c, &text);
    column += width;
  }
  return text;
}

static std::string WithoutTrailingBlanks(std::string_view text) {
  std::string kept;
  kept.reserve(text.size());
  std::string blanks;
  for (char c : text) {
    if (c == ' ' || c == '\t') {
      blanks.push_back(c);
      continue;
    }
    if (c != '\n' && c != '\r') kept += blanks;
    blanks.clear();
    kept.push_back(c);
  }
  return kept;
}

bool DecodeQuotedPrintable(std::string_view text, std::string* bytes) {
  const std::string kRead = WithoutTrailingBlanks(text);
  std::string decoded;
  size_t i = 0;
  while (i < kRead.size()) {
    if (kRead[i] == '\n' || kRead[i] == '\r') {
      ++i;
      continue;
    }
    if (kRead[i] != '=') {
      decoded.push_back(kRead[i]);
      ++i;
      continue;
    }
    if (!AppendQuotedPrintableEscape(kRead, &i, &decoded)) return false;
  }
  bytes->assign(decoded);
  return true;
}

}  // namespace delta
