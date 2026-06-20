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

std::pair<char, size_t> ParseOctal(std::string_view s, size_t pos) {
  int val = 0;
  size_t count = 0;
  while (count < 3 && pos + count < s.size() && IsOctalDigit(s[pos + count])) {
    val = val * 8 + (s[pos + count] - '0');
    ++count;
  }
  return {static_cast<char>(val), count};
}

std::pair<char, size_t> ParseHex(std::string_view s, size_t pos) {
  int val = 0;
  size_t count = 0;
  while (count < 2 && pos + count < s.size() && IsHexDigit(s[pos + count])) {
    val = val * 16 + HexVal(s[pos + count]);
    ++count;
  }
  return {static_cast<char>(val), count};
}

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

size_t ProcessEscape(std::string_view raw, size_t i, std::string& out) {
  char c = raw[i];
  char named = NamedEscape(c);
  if (named != 0) {
    out += named;
    return 0;
  }
  if (c == '\n') return 0;
  if (c == '\r') {
    if (i + 1 < raw.size() && raw[i + 1] == '\n') return 1;
    return 0;
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
    return count - 1;
  }
  out += c;
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
    ++i;
    if (i >= raw.size()) break;
    i += ProcessEscape(raw, i, result);
  }
  return result;
}

}  // namespace delta
