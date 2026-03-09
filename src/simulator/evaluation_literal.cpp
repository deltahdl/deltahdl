#include <cmath>
#include <cstring>
#include <string>
#include <vector>

#include "common/arena.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

namespace delta {

static bool IsXChar(char c) { return c == 'x' || c == 'X'; }
static bool IsZChar(char c) { return c == 'z' || c == 'Z' || c == '?'; }

static uint32_t LiteralWidth(std::string_view text, uint64_t val) {
  auto tick = text.find('\'');
  if (tick != std::string_view::npos && tick > 0) {
    uint32_t w = 0;
    for (size_t i = 0; i < tick; ++i) {
      if (text[i] >= '0' && text[i] <= '9') w = w * 10 + (text[i] - '0');
    }
    if (w > 0) return w;
  }
  return (val > UINT32_MAX) ? 64 : 32;
}
Logic4Vec EvalUnbasedUnsized(const Expr* expr, Arena& arena) {
  // §5.7.1: '0, '1, 'x, 'z — return 64-bit fill pattern for ResizeToWidth.
  auto text = expr->text;
  if (text.size() >= 2 && text[0] == '\'') {
    char c = text[1];
    if (c == '1') return MakeLogic4VecVal(arena, 64, ~uint64_t{0});
    if (c == '0') return MakeLogic4VecVal(arena, 64, 0);
    auto vec = MakeLogic4Vec(arena, 64);
    if (c == 'x' || c == 'X') vec.words[0] = {~uint64_t{0}, ~uint64_t{0}};
    if (c == 'z' || c == 'Z' || c == '?') vec.words[0] = {0, ~uint64_t{0}};
    return vec;
  }
  return MakeLogic4VecVal(arena, 64, expr->int_val);
}
static bool TextHasXZ(std::string_view text) {
  auto tick = text.find('\'');
  if (tick == std::string_view::npos) return false;
  for (size_t i = tick + 1; i < text.size(); ++i)
    if (IsXChar(text[i]) || IsZChar(text[i])) return true;
  return false;
}
// Bits per digit for each base letter.
static int BitsPerDigit(char base_letter) {
  switch (base_letter) {
    case 'h':
    case 'H':
      return 4;
    case 'o':
    case 'O':
      return 3;
    case 'b':
    case 'B':
      return 1;
    default:
      return 0;
  }
}
// Parse a digit's numeric value (0-15), or -1 for x/z.
static int DigitValue(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}
// Set bit_count bits starting at bit_pos in vec for an x/z/normal digit.
static void SetDigitBits(Logic4Vec& vec, uint32_t& bit_pos, int bit_count,
                         char digit, uint32_t width) {
  bool is_x = IsXChar(digit);
  bool is_z = IsZChar(digit);
  int dval = DigitValue(digit);
  for (int b = 0; b < bit_count && bit_pos < width; ++b, ++bit_pos) {
    uint32_t word = bit_pos / 64;
    uint64_t mask = uint64_t{1} << (bit_pos % 64);
    if (is_x) {
      vec.words[word].aval |= mask;
      vec.words[word].bval |= mask;
    } else if (is_z) {
      vec.words[word].bval |= mask;
    } else if (dval >= 0 && (dval & (1 << b))) {
      vec.words[word].aval |= mask;
    }
  }
}
static void FillXZ(Logic4Vec& vec, uint32_t start, uint32_t end, bool is_x) {
  for (uint32_t b = start; b < end; ++b) {
    uint32_t word = b / 64;
    uint64_t mask = uint64_t{1} << (b % 64);
    if (is_x) vec.words[word].aval |= mask;
    vec.words[word].bval |= mask;
  }
}
static size_t ParseLiteralBase(std::string_view text, std::string& buf,
                               int& bpd) {
  buf.clear();
  buf.reserve(text.size());
  for (char c : text)
    if (c != '_' && c != ' ' && c != '\t') buf.push_back(c);
  auto tick = buf.find('\'');
  if (tick == std::string::npos) return 0;
  size_t i = tick + 1;
  if (i < buf.size() && (buf[i] == 's' || buf[i] == 'S')) ++i;
  bpd = (i < buf.size()) ? BitsPerDigit(buf[i]) : 0;
  return i;
}
static Logic4Vec ParseBasedXZLiteral(std::string_view text, uint32_t width,
                                     Arena& arena) {
  auto vec = MakeLogic4Vec(arena, width);
  std::string buf;
  int bpd = 0;
  size_t i = ParseLiteralBase(text, buf, bpd);
  if (i == 0) return vec;
  if (bpd == 0) {
    // §5.7.1: Decimal single-digit x/z fills all bits.
    ++i;
    char first = (i < buf.size()) ? buf[i] : '\0';
    if (IsXChar(first) || IsZChar(first)) FillXZ(vec, 0, width, IsXChar(first));
    return vec;
  }
  ++i;
  uint32_t bit_pos = 0;
  for (auto j = buf.size(); j > i && bit_pos < width; --j)
    SetDigitBits(vec, bit_pos, bpd, buf[j - 1], width);
  // §5.7.1: Left-pad remaining bits with x or z if leftmost digit is x/z.
  if (bit_pos < width && i < buf.size()) {
    char lm = buf[i];
    if (IsXChar(lm) || IsZChar(lm)) FillXZ(vec, bit_pos, width, IsXChar(lm));
  }
  return vec;
}
static bool IsSignedLiteral(std::string_view text) {
  auto tick = text.find('\'');
  if (tick == std::string_view::npos || tick + 1 >= text.size()) return false;
  char c = text[tick + 1];
  return c == 's' || c == 'S';
}
Logic4Vec EvalIntLiteral(const Expr* expr, Arena& arena) {
  uint32_t width = LiteralWidth(expr->text, expr->int_val);
  bool is_signed = IsSignedLiteral(expr->text);
  if (TextHasXZ(expr->text)) {
    auto vec = ParseBasedXZLiteral(expr->text, width, arena);
    vec.is_signed = is_signed;
    return vec;
  }
  auto vec = MakeLogic4VecVal(arena, width, expr->int_val);
  vec.is_signed = is_signed;
  return vec;
}
// §5.9.1: Decode hex digit or return -1.
static int HexDigitVal(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}
// §5.9.1 Table 5-1: Map single-char escape to its value, or 0 if not simple.
static uint8_t SimpleEscapeChar(char c) {
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
// §5.9.1: Parse \xdd hex escape, advancing i past consumed digits.
static uint8_t ParseHexEscape(std::string_view text, size_t& i) {
  uint8_t val = 0;
  for (int j = 0; j < 2 && i + 1 < text.size(); ++j) {
    int d = HexDigitVal(text[i + 1]);
    if (d < 0) break;
    val = val * 16 + static_cast<uint8_t>(d);
    ++i;
  }
  return val;
}
// §5.9.1: Parse \ddd octal escape starting with first digit c.
static uint8_t ParseOctalEscape(char c, std::string_view text, size_t& i) {
  auto val = static_cast<uint8_t>(c - '0');
  for (int j = 0;
       j < 2 && i + 1 < text.size() && text[i + 1] >= '0' && text[i + 1] <= '7';
       ++j)
    val = val * 8 + static_cast<uint8_t>(text[++i] - '0');
  return val;
}
// §5.9.1: Decode string escape sequences into raw bytes.
static std::vector<uint8_t> DecodeStringBody(std::string_view text) {
  std::vector<uint8_t> bytes;
  for (size_t i = 0; i < text.size(); ++i) {
    if (text[i] != '\\' || i + 1 >= text.size()) {
      bytes.push_back(static_cast<uint8_t>(text[i]));
      continue;
    }
    char c = text[++i];
    uint8_t esc = SimpleEscapeChar(c);
    if (esc) {
      bytes.push_back(esc);
      continue;
    }
    if (c == 'x') {
      bytes.push_back(ParseHexEscape(text, i));
      continue;
    }
    if (c >= '0' && c <= '7') {
      bytes.push_back(ParseOctalEscape(c, text, i));
      continue;
    }
    if (c == '\n') continue;
    bytes.push_back(static_cast<uint8_t>(c));
  }
  return bytes;
}
Logic4Vec EvalStringLiteral(const Expr* expr, Arena& arena) {
  auto text = expr->text;
  if (text.size() >= 6 && text.substr(0, 3) == "\"\"\"")
    text = text.substr(3, text.size() - 6);
  else if (text.size() >= 2 && text.front() == '"')
    text = text.substr(1, text.size() - 2);
  auto bytes = DecodeStringBody(text);
  uint32_t width = static_cast<uint32_t>(bytes.size()) * 8;
  if (width == 0) width = 8;
  auto vec = MakeLogic4Vec(arena, width);
  for (size_t i = 0; i < bytes.size(); ++i) {
    auto byte_idx = static_cast<uint32_t>(bytes.size() - 1 - i);
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    vec.words[word].aval |= static_cast<uint64_t>(bytes[i]) << bit;
  }
  return vec;
}

}  // namespace delta
