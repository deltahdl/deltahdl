// The bits of a constant past the 64 that ConstVal::value holds. §5.7.1
// (printed page 77 of ~/LRM.pdf) sizes a based literal by its size constant
// and §6.20.2 (printed 126) gives a parameter its declared range, so a
// constant expression can be wider than the int64 the fold carries; §11.5.1
// (printed 296) then lets a select name any bit of it, and §11.4.10 with
// §11.4.8 shift it or combine it bit by bit. This file is where those bits
// are produced from a literal's digits and where they are read.

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "elaborator/const_eval_internal.h"
#include "lexer/token.h"

namespace delta {
namespace {

// The value of one digit character of an integer literal, or a value no base
// admits for a character that is no digit: an x, z or ? digit, which §5.7.1
// sets to the unknown or high-impedance value rather than to a number.
// LiteralDigitValue in src/parser/expr_parser.cpp is the same table; it is
// static there, and the elaborator takes the parser's syntax tree rather than
// its helpers.
uint64_t LiteralDigitValue(char c) {
  if (c >= '0' && c <= '9') return static_cast<uint64_t>(c - '0');
  if (c >= 'a' && c <= 'f') return static_cast<uint64_t>(c - 'a' + 10);
  if (c >= 'A' && c <= 'F') return static_cast<uint64_t>(c - 'A' + 10);
  return 99;
}

// §5.7.1: the base a literal's base format character names, read in either
// case, 10 for `'d`.
uint64_t LiteralBase(char base_char) {
  switch (static_cast<char>(base_char | 0x20)) {
    case 'h':
      return 16;
    case 'b':
      return 2;
    case 'o':
      return 8;
    default:
      return 10;
  }
}

// The digits of a literal wider than 64 bits with the underscores dropped,
// and its base. §5.7.1's three tokens are the size, the apostrophe with its
// base format character and the digits; a literal past 64 bits has a size
// constant and so an apostrophe, and the lexer admits no apostrophe without a
// base format character after it, so both are found. The s designator between
// them changes the interpretation and not the bit pattern.
std::pair<std::string, uint64_t> LiteralDigits(std::string_view text) {
  std::string buf;
  buf.reserve(text.size());
  for (char c : text) {
    if (c != '_') buf.push_back(c);
  }
  size_t i = buf.find('\'') + 1;
  if ((buf[i] | 0x20) == 's') ++i;
  uint64_t base = LiteralBase(buf[i++]);
  return {buf.substr(i), base};
}

// One digit folded into a value held as 32-bit halves, least significant
// first: each half is multiplied by the base and the carry from the half
// below is added, which a uint64_t holds since a half times a base of at
// most 16 plus a carry stays below 2^37.
void MultiplyAddHalves(std::vector<uint32_t>& halves, uint64_t base,
                       uint64_t digit) {
  uint64_t carry = digit;
  for (uint32_t& half : halves) {
    uint64_t acc = uint64_t{half} * base + carry;
    half = static_cast<uint32_t>(acc);
    carry = acc >> 32;
  }
  while (carry != 0) {
    halves.push_back(static_cast<uint32_t>(carry));
    carry >>= 32;
  }
}

// The words a value held as halves makes, least significant first.
std::vector<uint64_t> WordsOfHalves(const std::vector<uint32_t>& halves) {
  std::vector<uint64_t> words;
  for (size_t i = 0; i < halves.size(); i += 2) {
    uint64_t upper = i + 1 < halves.size() ? uint64_t{halves[i + 1]} << 32 : 0;
    words.push_back(uint64_t{halves[i]} | upper);
  }
  return words;
}

// The words above the first of `words`, cut to `width` -- §5.7.1 truncates a
// value wider than its size from the left -- and with the empty top words
// dropped, which is ConstVal::high_words' layout. `width` is above 64, so
// there is at least one word to keep.
std::vector<uint64_t> HighWordsAt(std::vector<uint64_t> words, uint32_t width) {
  words.erase(words.begin());
  words.resize((width - 1) / 64, 0);
  uint32_t top_bits = width % 64;
  if (top_bits != 0) words.back() &= ~uint64_t{0} >> (64 - top_bits);
  while (!words.empty() && words.back() == 0) words.pop_back();
  return words;
}

// Word `k` of `v`, word 0 being `value` and the rest ConstVal::high_words;
// 0 above the words the value carries.
uint64_t WordAt(const ConstVal& v, size_t k) {
  if (k == 0) return static_cast<uint64_t>(v.value);
  return k - 1 < v.high_words.size() ? v.high_words[k - 1] : 0;
}

// The words of `v` as a vector, enough of them for `width` bits, so the wide
// operators below can work word by word.
std::vector<uint64_t> WordsOf(const ConstVal& v, uint32_t width) {
  std::vector<uint64_t> words((width + 63) / 64, 0);
  for (size_t i = 0; i < words.size(); ++i) words[i] = WordAt(v, i);
  return words;
}

// The ConstVal `words` make at `width`: the first word is `value`, and the
// rest are cut to the width and trimmed as HighWordsAt cuts and trims them.
ConstVal ConstValOfWords(const std::vector<uint64_t>& words, uint32_t width,
                         bool is_signed) {
  return ConstVal{static_cast<int64_t>(words[0]), width, is_signed,
                  HighWordsAt(words, width)};
}

// §11.4.10: the words of `words` shifted left by `n` bits, the vacated low
// bits filled with 0. Each word takes the word `n / 64` below it, shifted up
// by the remaining bits, with the top of the word below that one.
std::vector<uint64_t> ShiftWordsLeft(const std::vector<uint64_t>& words,
                                     uint64_t n) {
  size_t word_shift = n / 64;
  uint64_t bit_shift = n % 64;
  std::vector<uint64_t> out(words.size(), 0);
  for (size_t i = 0; i < out.size(); ++i) {
    uint64_t lo = i >= word_shift ? words[i - word_shift] : 0;
    uint64_t below = i >= word_shift + 1 ? words[i - word_shift - 1] : 0;
    out[i] =
        bit_shift == 0 ? lo : (lo << bit_shift) | (below >> (64 - bit_shift));
  }
  return out;
}

// §11.4.10: the words of `words` shifted right by `n` bits, the vacated high
// bits filled with 0. Each word takes the word `n / 64` above it, shifted
// down by the remaining bits, with the bottom of the word above that one.
std::vector<uint64_t> ShiftWordsRight(const std::vector<uint64_t>& words,
                                      uint64_t n) {
  size_t count = words.size();
  size_t word_shift = n / 64;
  uint64_t bit_shift = n % 64;
  std::vector<uint64_t> out(count, 0);
  for (size_t i = 0; i < count; ++i) {
    size_t src = i + word_shift;
    uint64_t lo = src < count ? words[src] : 0;
    uint64_t above = src + 1 < count ? words[src + 1] : 0;
    out[i] =
        bit_shift == 0 ? lo : (lo >> bit_shift) | (above << (64 - bit_shift));
  }
  return out;
}

// §11.4.10: an arithmetic right shift of a signed operand fills the vacated
// bits with the sign bit, so the `n` bits from the top of `width` down are
// set after the logical shift where that bit was 1.
void FillTopBits(std::vector<uint64_t>& words, uint32_t width, uint64_t n) {
  for (uint64_t b = width - n; b < width; ++b) {
    words[b / 64] |= uint64_t{1} << (b % 64);
  }
}

// §11.4.10: the words of `lhs` shifted by `rhs`, which is self-determined and
// read as an unsigned count whatever its width; a count of the width or more
// leaves nothing of the operand, or the sign fill alone. Empty for an operator
// that is not a shift.
std::optional<std::vector<uint64_t>> WideShift(TokenKind op,
                                               const ConstVal& lhs,
                                               const ConstVal& rhs,
                                               uint32_t width) {
  uint64_t n = std::min(static_cast<uint64_t>(rhs.value), uint64_t{width});
  std::vector<uint64_t> words = WordsOf(lhs, width);
  switch (op) {
    case TokenKind::kLtLt:
    case TokenKind::kLtLtLt:
      return ShiftWordsLeft(words, n);
    case TokenKind::kGtGt:
      return ShiftWordsRight(words, n);
    case TokenKind::kGtGtGt: {
      std::vector<uint64_t> shifted = ShiftWordsRight(words, n);
      if (lhs.is_signed && ConstValBit(lhs, lhs.width - 1))
        FillTopBits(shifted, width, n);
      return shifted;
    }
    default:
      return std::nullopt;
  }
}

// §11.4.8: the words of `lhs` and `rhs` combined bit by bit; empty for an
// operator that is not one of the four bitwise ones.
std::optional<std::vector<uint64_t>> WideBitwise(TokenKind op,
                                                 const ConstVal& lhs,
                                                 const ConstVal& rhs,
                                                 uint32_t width) {
  std::vector<uint64_t> l = WordsOf(lhs, width);
  std::vector<uint64_t> r = WordsOf(rhs, width);
  for (size_t i = 0; i < l.size(); ++i) {
    switch (op) {
      case TokenKind::kAmp:
        l[i] &= r[i];
        break;
      case TokenKind::kPipe:
        l[i] |= r[i];
        break;
      case TokenKind::kCaret:
        l[i] ^= r[i];
        break;
      case TokenKind::kTildeCaret:
      case TokenKind::kCaretTilde:
        l[i] = ~(l[i] ^ r[i]);
        break;
      default:
        return std::nullopt;
    }
  }
  return l;
}

}  // namespace

std::vector<uint64_t> LiteralHighWords(std::string_view text, uint32_t width) {
  if (width <= 64) return {};
  auto [digits, base] = LiteralDigits(text);
  std::vector<uint32_t> halves{0};
  for (char c : digits) {
    uint64_t d = LiteralDigitValue(c);
    if (d >= base) break;
    MultiplyAddHalves(halves, base, d);
  }
  return HighWordsAt(WordsOfHalves(halves), width);
}

bool ConstValBit(const ConstVal& v, int64_t offset) {
  if (offset < 0) return false;
  auto bit = static_cast<uint64_t>(offset);
  return ((WordAt(v, bit / 64) >> (bit % 64)) & 1) != 0;
}

uint64_t ConstValWindow(const ConstVal& v, int64_t lo) {
  // A window below bit 0 is asked for by a part-select running off the
  // bottom of the value, whose upper bound is in range and whose width is
  // under 64 (SelectBitRange in const_eval.cpp), so -lo is under 64 here.
  if (lo < 0) return WordAt(v, 0) << -lo;
  auto start = static_cast<uint64_t>(lo);
  uint64_t shift = start % 64;
  uint64_t low = WordAt(v, start / 64) >> shift;
  if (shift == 0) return low;
  return low | (WordAt(v, start / 64 + 1) << (64 - shift));
}

std::optional<ConstVal> EvalWideBinary(TokenKind op, const ConstVal& lhs,
                                       const ConstVal& rhs, uint32_t width) {
  bool is_signed = lhs.is_signed && rhs.is_signed;
  if (auto shifted = WideShift(op, lhs, rhs, width))
    return ConstValOfWords(*shifted, width, is_signed);
  if (auto combined = WideBitwise(op, lhs, rhs, width))
    return ConstValOfWords(*combined, width, is_signed);
  return std::nullopt;
}

}  // namespace delta
