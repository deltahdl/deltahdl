#include "lexer/string_escape.h"

namespace delta {
namespace {

bool IsOctalDigit(char c) { return c >= '0' && c <= '7'; }

bool IsHexDigit(char c) {
  return (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') ||
         (c >= 'A' && c <= 'F');
}

int HexVal(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  return c - 'A' + 10;
}

// Parse 1–3 octal digits starting at pos. Returns (value, chars_consumed).
std::pair<char, size_t> ParseOctal(std::string_view s, size_t pos) {
  int val = 0;
  size_t count = 0;
  while (count < 3 && pos + count < s.size() && IsOctalDigit(s[pos + count])) {
    val = val * 8 + (s[pos + count] - '0');
    ++count;
  }
  return {static_cast<char>(val), count};
}

// Parse 1–2 hex digits starting at pos. Returns (value, chars_consumed).
std::pair<char, size_t> ParseHex(std::string_view s, size_t pos) {
  int val = 0;
  size_t count = 0;
  while (count < 2 && pos + count < s.size() && IsHexDigit(s[pos + count])) {
    val = val * 16 + HexVal(s[pos + count]);
    ++count;
  }
  return {static_cast<char>(val), count};
}

}  // namespace

std::string InterpretStringEscapes(std::string_view raw) {
  std::string result;
  result.reserve(raw.size());
  for (size_t i = 0; i < raw.size(); ++i) {
    if (raw[i] != '\\') {
      result += raw[i];
      continue;
    }
    ++i;  // skip backslash
    if (i >= raw.size()) break;
    char c = raw[i];
    switch (c) {
      case 'n':
        result += '\n';
        break;
      case 't':
        result += '\t';
        break;
      case '\\':
        result += '\\';
        break;
      case '"':
        result += '"';
        break;
      case 'v':
        result += '\v';
        break;
      case 'f':
        result += '\f';
        break;
      case 'a':
        result += '\a';
        break;
      case 'x': {
        auto [val, count] = ParseHex(raw, i + 1);
        if (count > 0) {
          result += val;
          i += count;
        } else {
          result += 'x';  // \x with no digits → literal x
        }
        break;
      }
      default:
        if (IsOctalDigit(c)) {
          auto [val, count] = ParseOctal(raw, i);
          result += val;
          i += count - 1;  // -1 because loop increments i
        } else {
          result += c;  // Unknown escape: drop backslash (§5.9.1)
        }
        break;
    }
  }
  return result;
}

}  // namespace delta
