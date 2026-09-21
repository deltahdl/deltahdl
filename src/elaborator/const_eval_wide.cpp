// The bits of a constant past the 64 that ConstVal::value holds. §5.7.1
// (printed page 77 of ~/IEEE 1800-2023.pdf) sizes a based literal by its size
// constant and §6.20.2 (printed 126) gives a parameter its declared range, so a
// constant expression can be wider than the int64 the fold carries; §11.5.1
// (printed 296) then lets a select name any bit of it, §11.4.10 with §11.4.8
// shift it or combine it bit by bit, §11.4.3 (printed 275-277) add to it,
// §11.4.4 and §11.4.5 (printed 278-279) compare it, §11.4.7 (printed 280)
// test it, §11.4.12 (printed 286-288) join it and §6.24.1 (printed 139) cast
// it. This file is where those bits are produced from a literal's digits and
// where they are read; const_eval_wide_arith.cpp multiplies, divides and
// raises them over the word helpers this file defines. Every shift folds
// here whatever its width, since §11.4.10 reads the count as an unsigned
// number of any size and §11.6.1's Table 11-21 (printed 299-300) sizes the
// result by the left operand alone, so a count can be wider than the value
// it shifts and larger than any C++ shift admits.

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"

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
  if (c >= 'a' && c <= 'f') return static_cast<uint64_t>(c - 'a') + 10;
  if (c >= 'A' && c <= 'F') return static_cast<uint64_t>(c - 'A') + 10;
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

// The words of `v` as a vector, enough of them for `width` bits and never
// fewer than one, so the wide operators below can work word by word and
// read a first word of a value of no bits, which a replication with a
// multiplier of zero is (§11.4.12.1).
std::vector<uint64_t> WordsOf(const ConstVal& v, uint32_t width) {
  std::vector<uint64_t> words(std::max<size_t>(1, (width + 63) / 64), 0);
  for (size_t i = 0; i < words.size(); ++i) words[i] = WordAt(v, i);
  return words;
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

// §11.4.10 (printed 284): the count `rhs` gives a shift of a value `width`
// bits wide, read as an unsigned number whatever its declaration and across
// every word of it, and cut to the width, since a count of the width or more
// leaves nothing of the value whichever it is: one with a bit set past its
// first word is that large. 64b2dfbe0 read `value` alone, which for a signed
// count under 64 bits carries its sign fill, and for one wider than 64 bits
// is its low word.
uint64_t ShiftCount(const ConstVal& rhs, uint32_t width) {
  std::vector<uint64_t> words = ExtendedWords(rhs, rhs.width, false);
  for (size_t i = 1; i < words.size(); ++i) {
    if (words[i] != 0) return width;
  }
  return std::min(words[0], uint64_t{width});
}

// §11.4.10: the words of `lhs` shifted by `rhs`, which is self-determined and
// read as an unsigned count whatever its width; a count of the width or more
// leaves nothing of the operand, or the sign fill alone. The left operand is
// read at its own width and no wider, `width` being that width by Table
// 11-21, so the sign fill a signed value under 64 bits carries above its
// width in `value` is not what a logical right shift brings down into it.
// The compound assignment forms are the shifts themselves. Empty for an
// operator that is not a shift.
std::optional<std::vector<uint64_t>> WideShift(TokenKind op,
                                               const ConstVal& lhs,
                                               const ConstVal& rhs,
                                               uint32_t width) {
  uint64_t n = ShiftCount(rhs, width);
  std::vector<uint64_t> words = ExtendedWords(lhs, width, false);
  switch (op) {
    case TokenKind::kLtLt:
    case TokenKind::kLtLtEq:
    case TokenKind::kLtLtLt:
    case TokenKind::kLtLtLtEq:
      return ShiftWordsLeft(words, n);
    case TokenKind::kGtGt:
    case TokenKind::kGtGtEq:
      return ShiftWordsRight(words, n);
    case TokenKind::kGtGtGt:
    case TokenKind::kGtGtGtEq: {
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
// operator that is not one of the four bitwise ones. A narrower operand is
// extended to the width by its sign where both are signed, which
// 64b2dfbe0's WordsOf, filling with zeros whatever the signedness, did not.
std::optional<std::vector<uint64_t>> WideBitwise(TokenKind op,
                                                 const ConstVal& lhs,
                                                 const ConstVal& rhs,
                                                 uint32_t width) {
  bool is_signed = lhs.is_signed && rhs.is_signed;
  std::vector<uint64_t> l = ExtendedWords(lhs, width, is_signed);
  std::vector<uint64_t> r = ExtendedWords(rhs, width, is_signed);
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

// §11.4.3 (printed 275): the words of `lhs` plus or minus those of `rhs`,
// carried and borrowed across every word. Empty for any other operator; the
// four multiplicative operators are EvalWideMultiplicative's.
std::optional<std::vector<uint64_t>> WideAddSub(TokenKind op,
                                                const ConstVal& lhs,
                                                const ConstVal& rhs,
                                                uint32_t width) {
  if (op != TokenKind::kPlus && op != TokenKind::kMinus) return std::nullopt;
  bool is_signed = lhs.is_signed && rhs.is_signed;
  std::vector<uint64_t> l = ExtendedWords(lhs, width, is_signed);
  std::vector<uint64_t> r = ExtendedWords(rhs, width, is_signed);
  if (op == TokenKind::kMinus) NegateWords(r);
  AddWords(l, r);
  return l;
}

// How two values stand to each other: whether the first is below the second,
// and whether the two are equal, which between them answer every relational
// and equality operator.
struct WideOrder {
  bool less;
  bool equal;
};

// §11.4.4 (printed 278) and §11.4.5 (printed 279): `l` against `r`, both of
// `width` bits, as signed values where `is_signed` -- the sign being the top
// bit at the width, so two values of one sign order as their bit patterns do
// -- and as unsigned values otherwise, word by word from the top.
WideOrder CompareWords(const std::vector<uint64_t>& l,
                       const std::vector<uint64_t>& r, uint32_t width,
                       bool is_signed) {
  uint64_t top = width - 1;
  bool l_neg = is_signed && ((l[top / 64] >> (top % 64)) & 1) != 0;
  bool r_neg = is_signed && ((r[top / 64] >> (top % 64)) & 1) != 0;
  if (l_neg != r_neg) return {l_neg, false};
  for (size_t i = l.size(); i-- > 0;) {
    if (l[i] != r[i]) return {l[i] < r[i], false};
  }
  return {false, true};
}

// What a relational or equality operator answers from `order`; empty for an
// operator that is neither. The case equality and wildcard operators are left
// out as the 64-bit fold leaves them out.
std::optional<bool> OrderAnswers(TokenKind op, WideOrder order) {
  switch (op) {
    case TokenKind::kLt:
      return order.less;
    case TokenKind::kGt:
      return !order.less && !order.equal;
    case TokenKind::kLtEq:
      return order.less || order.equal;
    case TokenKind::kGtEq:
      return !order.less;
    case TokenKind::kEqEq:
      return order.equal;
    case TokenKind::kBangEq:
      return !order.equal;
    default:
      return std::nullopt;
  }
}

// §11.4.4 and §11.4.5: the one bit a relational or equality operator answers
// over every word of its operands, the narrower one extended as
// ExtendedWords extends it. Empty for any other operator.
std::optional<ConstVal> WideCompare(TokenKind op, const ConstVal& lhs,
                                    const ConstVal& rhs, uint32_t width) {
  bool is_signed = lhs.is_signed && rhs.is_signed;
  auto answer = OrderAnswers(
      op, CompareWords(ExtendedWords(lhs, width, is_signed),
                       ExtendedWords(rhs, width, is_signed), width, is_signed));
  if (!answer) return std::nullopt;
  return ConstVal{*answer ? 1 : 0, 1, false};
}

// §11.4.7 (printed 280): the one bit a logical operator answers from whether
// each operand is nonzero, read across every word of it. Empty for any other
// operator.
std::optional<ConstVal> WideLogical(TokenKind op, const ConstVal& lhs,
                                    const ConstVal& rhs) {
  bool l = ConstValIsNonZero(lhs);
  bool r = ConstValIsNonZero(rhs);
  std::optional<bool> answer;
  switch (op) {
    case TokenKind::kAmpAmp:
      answer = l && r;
      break;
    case TokenKind::kPipePipe:
      answer = l || r;
      break;
    case TokenKind::kArrow:
      answer = !l || r;
      break;
    case TokenKind::kLtDashGt:
      answer = l == r;
      break;
    default:
      return std::nullopt;
  }
  return ConstVal{*answer ? 1 : 0, 1, false};
}

// §11.4.12 (printed 286-287): the words of `parts` joined at `width`, the
// sum of their widths, the first part the most significant. Each part
// contributes its own width of bits and nothing above them, so a signed
// part's sign fill is cut away by ExtendedWords.
std::vector<uint64_t> JoinedWords(const std::vector<ConstVal>& parts,
                                  uint32_t width) {
  std::vector<uint64_t> words((width + 63) / 64, 0);
  for (const ConstVal& part : parts) {
    words = ShiftWordsLeft(words, part.width);
    std::vector<uint64_t> own = ExtendedWords(part, width, false);
    for (size_t i = 0; i < words.size(); ++i) words[i] |= own[i];
  }
  return words;
}

// The unsigned value of `width` bits `parts` join to, and a value of no bits
// for no parts or parts of no width, which a replication with a multiplier of
// zero is (§11.4.12.1, printed 288).
ConstVal JoinedConstVal(const std::vector<ConstVal>& parts, uint32_t width) {
  if (width == 0) return ConstVal{0, 0, false};
  return ConstValOfWords(JoinedWords(parts, width), width, false);
}

// The most bits a replication is let grow to at elaboration; a multiplier
// taking the value past it leaves the fold unanswered rather than allocating
// without bound.
constexpr uint64_t kMaxReplicationBits = uint64_t{1} << 20;

}  // namespace

std::vector<uint64_t> WordsOfHalves(const std::vector<uint32_t>& halves) {
  std::vector<uint64_t> words;
  for (size_t i = 0; i < halves.size(); i += 2) {
    uint64_t upper = i + 1 < halves.size() ? uint64_t{halves[i + 1]} << 32 : 0;
    words.push_back(uint64_t{halves[i]} | upper);
  }
  return words;
}

// A signed value under 64 bits holds its sign fill in `value`
// (NormalizeConstVal), which is what an operand read as unsigned or joined
// into a concatenation must not carry, and what this clears.
void ClearBitsFrom(std::vector<uint64_t>& words, uint32_t width) {
  for (size_t i = 0; i < words.size(); ++i) {
    uint64_t base = 64 * i;
    if (base >= width) {
      words[i] = 0;
    } else if (width - base < 64) {
      words[i] &= ~uint64_t{0} >> (64 - (width - base));
    }
  }
}

// The words above the first are cut and trimmed as HighWordsAt cuts and
// trims them, there being none to keep at 64 bits or less.
ConstVal ConstValOfWords(const std::vector<uint64_t>& words, uint32_t width,
                         bool is_signed) {
  ConstVal v =
      NormalizeConstVal(static_cast<int64_t>(words[0]), width, is_signed);
  if (width > 64) v.high_words = HighWordsAt(words, width);
  return v;
}

// The words below 64 of a signed value under 64 bits already hold its sign
// fill (NormalizeConstVal), which ClearBitsFrom removes and the fill puts
// back only where it belongs.
std::vector<uint64_t> ExtendedWords(const ConstVal& v, uint32_t width,
                                    bool sign_extend) {
  std::vector<uint64_t> words = WordsOf(v, width);
  ClearBitsFrom(words, v.width);
  if (sign_extend && v.width < width && ConstValBit(v, v.width - 1))
    FillTopBits(words, width, width - v.width);
  return words;
}

// The dropped carry is the truncation §11.6.1 gives a sum evaluated at the
// width of its operands.
void AddWords(std::vector<uint64_t>& acc, const std::vector<uint64_t>& addend) {
  uint64_t carry = 0;
  for (size_t i = 0; i < acc.size(); ++i) {
    uint64_t sum = acc[i] + addend[i];
    uint64_t carry_out = sum < acc[i] ? 1 : 0;
    uint64_t total = sum + carry;
    carry_out += total < sum ? 1 : 0;
    acc[i] = total;
    carry = carry_out;
  }
}

// Also what a subtraction adds in place of its second operand.
void NegateWords(std::vector<uint64_t>& words) {
  for (uint64_t& w : words) w = ~w;
  std::vector<uint64_t> one(words.size(), 0);
  if (!one.empty()) one[0] = 1;
  AddWords(words, one);
}

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

bool ConstValIsNonZero(const ConstVal& v) {
  if (v.value != 0) return true;
  for (uint64_t w : v.high_words) {
    if (w != 0) return true;
  }
  return false;
}

// A shift's result is signed where its left operand is (§11.4.10, printed
// 284), the count being self-determined; 64b2dfbe0 asked both operands.
std::optional<ConstVal> EvalWideBinary(TokenKind op, const ConstVal& lhs,
                                       const ConstVal& rhs, uint32_t width) {
  bool is_signed = BinaryResultSigned(op, lhs, rhs);
  switch (op) {
    case TokenKind::kStar:
    case TokenKind::kSlash:
    case TokenKind::kPercent:
    case TokenKind::kPower:
      return EvalWideMultiplicative(op, lhs, rhs, width);
    default:
      break;
  }
  if (auto shifted = WideShift(op, lhs, rhs, width))
    return ConstValOfWords(*shifted, width, is_signed);
  if (auto combined = WideBitwise(op, lhs, rhs, width))
    return ConstValOfWords(*combined, width, is_signed);
  if (auto summed = WideAddSub(op, lhs, rhs, width))
    return ConstValOfWords(*summed, width, is_signed);
  if (auto compared = WideCompare(op, lhs, rhs, width)) return compared;
  return WideLogical(op, lhs, rhs);
}

std::optional<ConstVal> EvalWideUnary(TokenKind op, const ConstVal& operand) {
  std::vector<uint64_t> words = WordsOf(operand, operand.width);
  switch (op) {
    case TokenKind::kPlus:
      return operand;
    case TokenKind::kMinus:
      NegateWords(words);
      return ConstValOfWords(words, operand.width, operand.is_signed);
    case TokenKind::kTilde:
      for (uint64_t& w : words) w = ~w;
      return ConstValOfWords(words, operand.width, operand.is_signed);
    case TokenKind::kBang:
      return ConstVal{ConstValIsNonZero(operand) ? 0 : 1, 1, false};
    default:
      return std::nullopt;
  }
}

ConstVal CastConstVal(const ConstVal& v, uint32_t width, bool is_signed) {
  if (width <= 64) return NormalizeConstVal(v.value, width, is_signed);
  return ConstValOfWords(ExtendedWords(v, width, v.is_signed), width,
                         is_signed);
}

std::optional<ConstVal> ConstEvalConcatFull(const Expr* expr,
                                            const ScopeMap& scope) {
  std::vector<ConstVal> parts;
  uint32_t width = 0;
  for (const Expr* elem : expr->elements) {
    auto part = ConstEvalFull(elem, scope);
    if (!part) return std::nullopt;
    width += part->width;
    parts.push_back(*part);
  }
  return JoinedConstVal(parts, width);
}

std::optional<ConstVal> ConstEvalReplicateFull(const Expr* expr,
                                               const ScopeMap& scope) {
  auto count = ConstEvalInt(expr->repeat_count, scope);
  if (!count || *count < 0) return std::nullopt;
  auto inner = ConstEvalConcatFull(expr, scope);
  if (!inner) return std::nullopt;
  auto n = static_cast<uint64_t>(*count);
  if (n > kMaxReplicationBits || n * inner->width > kMaxReplicationBits)
    return std::nullopt;
  std::vector<ConstVal> copies(static_cast<size_t>(n), *inner);
  return JoinedConstVal(copies, static_cast<uint32_t>(n * inner->width));
}

}  // namespace delta
