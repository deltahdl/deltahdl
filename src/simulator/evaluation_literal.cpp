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

uint32_t LiteralWidth(std::string_view text, uint64_t val) {
  auto tick = text.find('\'');
  if (tick != std::string_view::npos && tick > 0) {
    uint32_t w = 0;
    for (size_t i = 0; i < tick; ++i) {
      if (text[i] >= '0' && text[i] <= '9') w = w * 10 + (text[i] - '0');
    }
    if (w > 0) return w;
  }
  // An unsized number is at least 32 bits, widened to the minimum width that
  // holds its value. §5.7.1 additionally requires a signed unsized number to
  // keep a sign bit, so a value whose most significant magnitude bit would
  // land on the sign position needs one extra bit to stay non-negative.
  if (val > UINT32_MAX) return 64;
  if (IsSignedLiteral(text) && val > uint64_t{0x7FFFFFFF}) return 33;
  return 32;
}
Logic4Vec EvalUnbasedUnsized(const Expr* expr, Arena& arena) {
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

static int DigitValue(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}

static void SetDigitBits(Logic4Vec& vec, uint32_t& bit_pos, int bit_count,
                         char digit, uint32_t width) {
  bool is_x = IsXChar(digit);
  bool is_z = IsZChar(digit);
  int dval = DigitValue(digit);
  for (int b = 0; b < bit_count && bit_pos < width; ++b, ++bit_pos) {
    uint32_t word = bit_pos / 64;
    uint64_t mask = uint64_t{1} << (bit_pos % 64);
    if (is_x) {
      // An x literal digit uses the (aval=1, bval=1) encoding.
      vec.words[word].aval |= mask;
      vec.words[word].bval |= mask;
    } else if (is_z) {
      // A z literal digit uses the (aval=0, bval=1) encoding, matching FillXZ
      // and the raw-bit consumers (see net.cpp GetBitVal).
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
    ++i;
    char first = (i < buf.size()) ? buf[i] : '\0';
    if (IsXChar(first) || IsZChar(first)) FillXZ(vec, 0, width, IsXChar(first));
    return vec;
  }
  ++i;
  uint32_t bit_pos = 0;
  for (auto j = buf.size(); j > i && bit_pos < width; --j)
    SetDigitBits(vec, bit_pos, bpd, buf[j - 1], width);

  if (bit_pos < width && i < buf.size()) {
    char lm = buf[i];
    if (IsXChar(lm) || IsZChar(lm)) FillXZ(vec, bit_pos, width, IsXChar(lm));
  }
  return vec;
}

static bool IsUnsizedLiteral(std::string_view text) {
  return !text.empty() && text.front() == '\'';
}

static bool MsbBvalSet(const Logic4Vec& vec, uint32_t width) {
  if (width == 0 || vec.nwords == 0) return false;
  uint32_t msb_word = (width - 1) / 64;
  uint64_t msb_mask = uint64_t{1} << ((width - 1) % 64);
  return (vec.words[msb_word].bval & msb_mask) != 0;
}

Logic4Vec EvalIntLiteral(const Expr* expr, Arena& arena) {
  uint32_t width = LiteralWidth(expr->text, expr->int_val);
  bool is_signed = IsSignedLiteral(expr->text);
  if (TextHasXZ(expr->text)) {
    auto vec = ParseBasedXZLiteral(expr->text, width, arena);
    vec.is_signed = is_signed;
    // An unsized literal whose high-order bit ended up as x or z must
    // propagate that high-order bit through any wider context the
    // value is used in. ResizeToWidth performs MSB-pattern extension
    // when is_signed is set, so we piggy-back on that mechanism here
    // without claiming the literal is signed for arithmetic — x/z
    // contaminate any operation regardless of signedness.
    if (IsUnsizedLiteral(expr->text) && MsbBvalSet(vec, width)) {
      vec.is_signed = true;
    }
    return vec;
  }
  // §5.7.1: a sized literal's value is formed from all its digits. A based
  // hex/octal/binary literal wider than 64 bits cannot be carried by the
  // single 64-bit expr->int_val the parser computes (its high words are lost
  // and its low word is corrupted by the parser's overflow), so parse the
  // digit string directly into a multi-word vector. ParseBasedXZLiteral
  // handles plain numeric digits in addition to x/z (none present here).
  if (width > 64) {
    std::string buf;
    int bpd = 0;
    ParseLiteralBase(expr->text, buf, bpd);
    if (bpd != 0) {
      auto vec = ParseBasedXZLiteral(expr->text, width, arena);
      vec.is_signed = is_signed;
      return vec;
    }
  }
  auto vec = MakeLogic4VecVal(arena, width, expr->int_val);
  vec.is_signed = is_signed;
  return vec;
}

static int HexDigitVal(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}

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

// A.8.8: the `\x one_to_two_digit_hex_number` alternative needs at least one
// hex digit after the x. Answers -1 when none follows, leaving the sequence to
// the `\any_ASCII_character` alternative rather than reading it as \x00.
static int ParseHexEscape(std::string_view text, size_t& i) {
  int val = -1;
  for (int j = 0; j < 2 && i + 1 < text.size(); ++j) {
    int d = HexDigitVal(text[i + 1]);
    if (d < 0) break;
    val = (val < 0 ? 0 : val) * 16 + d;
    ++i;
  }
  return val;
}

static uint8_t ParseOctalEscape(char c, std::string_view text, size_t& i) {
  auto val = static_cast<uint8_t>(c - '0');
  for (int j = 0;
       j < 2 && i + 1 < text.size() && text[i + 1] >= '0' && text[i + 1] <= '7';
       ++j)
    val = val * 8 + static_cast<uint8_t>(text[++i] - '0');
  return val;
}

// The byte a string_escape_seq beginning `\c` stands for, or -1 when it stands
// for no byte at all -- a backslash before a newline is a line continuation.
// A.8.8 lists `\any_ASCII_character` as an alternative in its own right, so
// every sequence the octal and hex alternatives do not match falls to it and
// spells the character itself. That is why an x with no hex digit after it is
// an ordinary x.
static int EscapeByte(char c, std::string_view text, size_t& i) {
  if (uint8_t esc = SimpleEscapeChar(c); esc != 0) return esc;
  if (c == 'x') {
    int hex = ParseHexEscape(text, i);
    return hex >= 0 ? hex : 'x';
  }
  if (c >= '0' && c <= '7') return ParseOctalEscape(c, text, i);
  if (c == '\n') return -1;
  return static_cast<unsigned char>(c);
}

static std::vector<uint8_t> DecodeStringBody(std::string_view text) {
  std::vector<uint8_t> bytes;
  for (size_t i = 0; i < text.size(); ++i) {
    if (text[i] != '\\' || i + 1 >= text.size()) {
      bytes.push_back(static_cast<uint8_t>(text[i]));
      continue;
    }
    ++i;
    int b = EscapeByte(text[i], text, i);
    if (b >= 0) bytes.push_back(static_cast<uint8_t>(b));
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
