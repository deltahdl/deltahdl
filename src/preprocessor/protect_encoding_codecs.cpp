#include "preprocessor/protect_encoding_codecs.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

namespace delta {
namespace {

// Two of the schemes write three bytes as four characters of a sixty-four
// character alphabet, differing only in which characters they draw on and in
// what they do with a final group that is short of three bytes. The
// transformation is written once and given the alphabet, so the two cannot
// drift apart in the part they share.
constexpr std::string_view kBase64Alphabet =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

// The alphabet of this implementation's own scheme. Nothing here closes a
// string value or opens a comment, so a block written with it survives being
// carried through source text as the value of a pragma expression.
constexpr std::string_view kBlockAlphabet =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_";

// What RFC 2045 fills a short final group out with, and the absence of any
// such character. A scheme that pads writes a block whose length is always a
// multiple of four; one that does not writes the two or three characters the
// short group needs and stops there.
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

// The last group of an encoded block may be short: three characters carry two
// bytes and two characters carry one. A single trailing character carries no
// whole byte, so a block that ends with one is not a block this transformation
// produced.
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

// The inverse of EncodeSixBitGroups. Fails on a character the alphabet does
// not hold and on a block that ends part way through a group, because neither
// can come out of the transformation and both mean the text is recording
// something else.
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

// The most data one line of the historical algorithm's output carries.
constexpr size_t kUuencodeMaxLineBytes = 45;

// The character standing for one six-bit value. The historical algorithm adds
// a space's value to it, which leaves a zero written as a space; the grave
// accent stands for the same value and is what is written here, so that a
// value carried on a line of its own does not lose characters to whatever
// trims the whitespace around it. A reading accepts either spelling.
char UuencodeChar(size_t value) {
  if (value == 0) return '`';
  return static_cast<char>(value + 0x20U);
}

// The value one such character stands for, and whether it is one at all. The
// characters the algorithm writes run from the space to the grave accent, and
// nothing outside that run came out of it.
bool UuencodeValueOf(char c, size_t* value) {
  auto byte = static_cast<unsigned char>(c);
  if (byte < 0x20U || byte > 0x60U) return false;
  *value = static_cast<size_t>((byte - 0x20U) & 0x3FU);
  return true;
}

// The data of one line, written six bits to a character. A final group short
// of three bytes is filled out with zeroes, the length character at the head
// of the line being what says how much of the group is data.
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

// How much data a line may carry if the characters standing for it, and the
// length character ahead of them, are to fit inside `line_length`. A length
// too small for even one group still gets one, a line carrying no data at all
// being the mark this algorithm ends its output with rather than a line the
// data can be written on.
size_t UuencodeBytesPerLine(size_t line_length) {
  if (line_length == 0) return kUuencodeMaxLineBytes;
  size_t groups = line_length < 5 ? 1 : (line_length - 1) / 4;
  return std::min(groups * 3, kUuencodeMaxLineBytes);
}

// Takes the data one line of the algorithm's output carries: `want` bytes,
// read four characters at a time out of `line`, which is the line after its
// length character. A line too short for the length it announced, or holding a
// character the algorithm never writes, records no data and is refused.
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

// The next line of `text` starting at `*pos`, without its terminator and
// without the carriage return a text written on another system leaves ahead of
// it, with `*pos` advanced past the line.
std::string_view NextLine(std::string_view text, size_t* pos) {
  size_t eol = text.find('\n', *pos);
  size_t end = eol == std::string_view::npos ? text.size() : eol;
  std::string_view line = text.substr(*pos, end - *pos);
  *pos = eol == std::string_view::npos ? text.size() : eol + 1;
  if (!line.empty() && line.back() == '\r') line.remove_suffix(1);
  return line;
}

// The longest line RFC 2045 allows, counting the equals sign that would break
// it.
constexpr size_t kQuotedPrintableMaxLine = 76;

// The shortest line that can hold one byte written as an equals sign and two
// hex digits, with room left for the sign that breaks the line.
constexpr size_t kQuotedPrintableMinLine = 4;

// RFC 2045 writes the two digits of a byte in capitals and lets a reading
// accept either case, so the writing draws on the first of these and the
// reading tries both.
constexpr std::string_view kHexDigits = "0123456789ABCDEF";
constexpr std::string_view kLowerHexDigits = "0123456789abcdef";

// Whether the byte is one RFC 2045 lets stand for itself: a printable
// character other than the equals sign, which the scheme has taken for its own
// use. A space and a tab are printable but may not end a line, so they are
// written out rather than left to fall wherever the breaking puts them.
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

// Reads whatever an equals sign at `*i` introduces: a soft line break, which
// stands for nothing in the data, or the two hex digits of one byte. Anything
// else is not something the scheme writes.
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

// The padding says how short the final group was, and the transformation that
// reads a short group reads that from the group's own length, so the padding
// is taken off before the reading rather than read as data.
bool DecodeBase64(std::string_view text, std::string* bytes) {
  while (!text.empty() && text.back() == kBase64Pad) text.remove_suffix(1);
  return DecodeSixBitGroups(text, kBase64Alphabet, bytes);
}

std::string EncodeProtectBlockAlphabet(std::string_view bytes) {
  return EncodeSixBitGroups(bytes, kBlockAlphabet, kNoPad);
}

bool DecodeProtectBlockAlphabet(std::string_view text, std::string* bytes) {
  return DecodeSixBitGroups(text, kBlockAlphabet, bytes);
}

// The output ends with a line carrying no data, which is how the algorithm
// says the data are complete. Written for data of no length that line is the
// whole of the output, and reading it back gives no data, which is what was
// written.
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

// A line is broken before the byte that would carry it past the limit, and the
// equals sign the break is written with is itself part of the line, so the
// room for it is reserved rather than taken from the next line.
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

bool DecodeQuotedPrintable(std::string_view text, std::string* bytes) {
  std::string decoded;
  size_t i = 0;
  while (i < text.size()) {
    if (text[i] == '\n' || text[i] == '\r') {
      ++i;
      continue;
    }
    if (text[i] != '=') {
      decoded.push_back(text[i]);
      ++i;
      continue;
    }
    if (!AppendQuotedPrintableEscape(text, &i, &decoded)) return false;
  }
  bytes->assign(decoded);
  return true;
}

}  // namespace delta
