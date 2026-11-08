#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/types.h"
#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"

namespace delta {
namespace {

uint64_t LiteralDigitValue(char c) {
  if (c >= '0' && c <= '9') return static_cast<uint64_t>(c - '0');
  if (c >= 'a' && c <= 'f') return static_cast<uint64_t>(c - 'a') + 10;
  if (c >= 'A' && c <= 'F') return static_cast<uint64_t>(c - 'A') + 10;
  return 99;
}

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

std::pair<std::string, uint64_t> LiteralDigits(std::string_view text) {
  std::string buf = LiteralTextWithoutSeparators(text);
  size_t i = buf.find('\'') + 1;
  if ((buf[i] | 0x20) == 's') ++i;
  uint64_t base = LiteralBase(buf[i++]);
  return {buf.substr(i), base};
}

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

std::vector<uint64_t> HighWordsAt(std::vector<uint64_t> words, uint32_t width) {
  words.erase(words.begin());
  words.resize((width - 1) / 64, 0);
  uint32_t top_bits = width % 64;
  if (top_bits != 0) words.back() &= ~uint64_t{0} >> (64 - top_bits);
  while (!words.empty() && words.back() == 0) words.pop_back();
  return words;
}

uint64_t WordAt(const ConstVal& v, size_t k) {
  if (k == 0) return static_cast<uint64_t>(v.value);
  return k - 1 < v.high_words.size() ? v.high_words[k - 1] : 0;
}

std::vector<uint64_t> WordsOf(const ConstVal& v, uint32_t width) {
  std::vector<uint64_t> words(std::max<size_t>(1, (width + 63) / 64), 0);
  for (size_t i = 0; i < words.size(); ++i) words[i] = WordAt(v, i);
  return words;
}

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

void FillTopBits(std::vector<uint64_t>& words, uint32_t width, uint64_t n) {
  for (uint64_t b = width - n; b < width; ++b) {
    words[b / 64] |= uint64_t{1} << (b % 64);
  }
}

uint64_t ShiftCount(const ConstVal& rhs, uint32_t width) {
  std::vector<uint64_t> words = ExtendedWords(rhs, rhs.width, false);
  for (size_t i = 1; i < words.size(); ++i) {
    if (words[i] != 0) return width;
  }
  return std::min(words[0], uint64_t{width});
}

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

struct WideOrder {
  bool less;
  bool equal;
};

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
    case TokenKind::kEqEqEq:
    case TokenKind::kEqEqQuestion:
      return order.equal;
    case TokenKind::kBangEq:
    case TokenKind::kBangEqEq:
    case TokenKind::kBangEqQuestion:
      return !order.equal;
    default:
      return std::nullopt;
  }
}

std::optional<ConstVal> WideCompare(TokenKind op, const ConstVal& lhs,
                                    const ConstVal& rhs, uint32_t width) {
  bool is_signed = lhs.is_signed && rhs.is_signed;
  auto answer = OrderAnswers(
      op, CompareWords(ExtendedWords(lhs, width, is_signed),
                       ExtendedWords(rhs, width, is_signed), width, is_signed));
  if (!answer) return std::nullopt;
  return ConstVal{*answer ? 1 : 0, 1, false};
}

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

ConstVal JoinedConstVal(const std::vector<ConstVal>& parts, uint32_t width) {
  if (width == 0) return ConstVal{0, 0, false};
  return ConstValOfWords(JoinedWords(parts, width), width, false);
}

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

ConstVal ConstValOfWords(const std::vector<uint64_t>& words, uint32_t width,
                         bool is_signed) {
  ConstVal v =
      NormalizeConstVal(static_cast<int64_t>(words[0]), width, is_signed);
  if (width > 64) v.high_words = HighWordsAt(words, width);
  return v;
}

std::vector<uint64_t> ExtendedWords(const ConstVal& v, uint32_t width,
                                    bool sign_extend) {
  std::vector<uint64_t> words = WordsOf(v, width);
  ClearBitsFrom(words, v.width);
  if (sign_extend && v.width < width && ConstValBit(v, v.width - 1))
    FillTopBits(words, width, width - v.width);
  return words;
}

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

void NegateWords(std::vector<uint64_t>& words) {
  for (uint64_t& w : words) w = ~w;
  std::vector<uint64_t> one(words.size(), 0);
  if (!one.empty()) one[0] = 1;
  AddWords(words, one);
}

static bool g_unknown_digits_as_zero = false;

TwoStateLiteralGuard::TwoStateLiteralGuard(bool on)
    : prev_(g_unknown_digits_as_zero) {
  g_unknown_digits_as_zero = on;
}

TwoStateLiteralGuard::~TwoStateLiteralGuard() {
  g_unknown_digits_as_zero = prev_;
}

bool UnknownDigitsReadAsZero() { return g_unknown_digits_as_zero; }

static bool IsUnknownDigit(char c) {
  return c == 'x' || c == 'X' || c == 'z' || c == 'Z' || c == '?';
}

static std::vector<uint64_t> WordsOfDigits(std::string_view digits,
                                           uint64_t base,
                                           bool unknown_as_zero) {
  std::vector<uint32_t> halves{0};
  for (char c : digits) {
    uint64_t d =
        unknown_as_zero && IsUnknownDigit(c) ? 0 : LiteralDigitValue(c);
    if (d >= base) break;
    MultiplyAddHalves(halves, base, d);
  }
  return WordsOfHalves(halves);
}

std::vector<uint64_t> LiteralHighWords(std::string_view text, uint32_t width) {
  if (width <= 64) return {};
  auto [digits, base] = LiteralDigits(text);
  return HighWordsAt(WordsOfDigits(digits, base, g_unknown_digits_as_zero),
                     width);
}

std::optional<uint64_t> BasedLiteralLowWord(std::string_view text) {
  std::string buf = LiteralTextWithoutSeparators(text);
  size_t tick = buf.find('\'');
  if (tick == std::string::npos) return std::nullopt;
  size_t i = tick + 1;
  if (i < buf.size() && (buf[i] == 's' || buf[i] == 'S')) ++i;
  if (i >= buf.size()) return std::nullopt;
  if (std::string_view("bBoOdDhH").find(buf[i]) == std::string_view::npos)
    return std::nullopt;
  return WordsOfDigits(std::string_view(buf).substr(i + 1), LiteralBase(buf[i]),
                       true)[0];
}

bool ConstValBit(const ConstVal& v, int64_t offset) {
  if (offset < 0) return false;
  auto bit = static_cast<uint64_t>(offset);
  return ((WordAt(v, bit / 64) >> (bit % 64)) & 1) != 0;
}

bool ConstValIsNonZero(const ConstVal& v) {
  if (v.value != 0) return true;
  for (uint64_t w : v.high_words) {
    if (w != 0) return true;
  }
  return false;
}

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
