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

// Parse 1-3 octal digits starting at pos. Returns (value, chars_consumed).
std::pair<char, size_t> ParseOctal(std::string_view s, size_t pos) {
  int val = 0;
  size_t count = 0;
  while (count < 3 && pos + count < s.size() && IsOctalDigit(s[pos + count])) {
    val = val * 8 + (s[pos + count] - '0');
    ++count;
  }
  return {static_cast<char>(val), count};
}

// Parse 1-2 hex digits starting at pos. Returns (value, chars_consumed).
std::pair<char, size_t> ParseHex(std::string_view s, size_t pos) {
  int val = 0;
  size_t count = 0;
  while (count < 2 && pos + count < s.size() && IsHexDigit(s[pos + count])) {
    val = val * 16 + HexVal(s[pos + count]);
    ++count;
  }
  return {static_cast<char>(val), count};
}

// Map a named escape character to its value. Returns 0 if not a named escape.
char NamedEscape(char c) {
  switch (c) {
    case 'n':
      return '\n';
    case 't':
      return '\t';
    case '\\':
      return '\\';
    case '"':
      return '"';
    case 'v':
      return '\v';
    case 'f':
      return '\f';
    case 'a':
      return '\a';
    default:
      return 0;
  }
}

// Process one escape sequence starting after the backslash.
// Appends the result to 'out' and returns the number of extra chars consumed.
size_t ProcessEscape(std::string_view raw, size_t i, std::string& out) {
  char c = raw[i];
  char named = NamedEscape(c);
  if (named != 0) {
    out += named;
    return 0;
  }
  if (c == '\n') return 0;  // §5.9 line continuation: both chars ignored
  if (c == '\r') {
    if (i + 1 < raw.size() && raw[i + 1] == '\n') return 1;  // skip \r\n
    return 0;  // bare \r continuation
  }
  if (c == 'x') {
    auto [val, count] = ParseHex(raw, i + 1);
    if (count > 0) {
      out += val;
      return count;
    }
    out += 'x';
    return 0;
  }
  if (IsOctalDigit(c)) {
    auto [val, count] = ParseOctal(raw, i);
    out += val;
    return count - 1;  // -1 because caller already consumed first char
  }
  out += c;  // Unknown escape: drop backslash (§5.9.1)
  return 0;
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
    i += ProcessEscape(raw, i, result);
  }
  return result;
}

}  // namespace delta
