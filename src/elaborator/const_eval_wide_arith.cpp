#include <cstddef>
#include <cstdint>
#include <optional>
#include <utility>
#include <vector>

#include "elaborator/const_eval_internal.h"
#include "lexer/token.h"

namespace delta {
namespace {

std::vector<uint32_t> HalvesOfWords(const std::vector<uint64_t>& words) {
  std::vector<uint32_t> halves;
  halves.reserve(words.size() * 2);
  for (uint64_t w : words) {
    halves.push_back(static_cast<uint32_t>(w));
    halves.push_back(static_cast<uint32_t>(w >> 32));
  }
  return halves;
}

std::vector<uint64_t> MultiplyWords(const std::vector<uint64_t>& l,
                                    const std::vector<uint64_t>& r) {
  std::vector<uint32_t> a = HalvesOfWords(l);
  std::vector<uint32_t> b = HalvesOfWords(r);
  std::vector<uint32_t> product(a.size(), 0);
  for (size_t i = 0; i < a.size(); ++i) {
    uint64_t carry = 0;
    for (size_t j = 0; i + j < a.size(); ++j) {
      uint64_t acc = uint64_t{a[i]} * b[j] + product[i + j] + carry;
      product[i + j] = static_cast<uint32_t>(acc);
      carry = acc >> 32;
    }
  }
  return WordsOfHalves(product);
}

bool WordsAreZero(const std::vector<uint64_t>& words) {
  for (uint64_t w : words) {
    if (w != 0) return false;
  }
  return true;
}

bool WordsAtLeast(const std::vector<uint64_t>& l,
                  const std::vector<uint64_t>& r) {
  for (size_t i = l.size(); i-- > 0;) {
    if (l[i] != r[i]) return l[i] > r[i];
  }
  return true;
}

bool TopBitSet(const std::vector<uint64_t>& words, uint32_t width) {
  uint32_t top = width - 1;
  return ((words[top / 64] >> (top % 64)) & 1) != 0;
}

std::vector<uint64_t> OneInWords(size_t count) {
  std::vector<uint64_t> one(count, 0);
  one[0] = 1;
  return one;
}

void ShiftInBit(std::vector<uint64_t>& words, uint64_t bit) {
  uint64_t carry = bit;
  for (uint64_t& w : words) {
    uint64_t top = w >> 63;
    w = (w << 1) | carry;
    carry = top;
  }
}

struct WideDivision {
  std::vector<uint64_t> quotient;
  std::vector<uint64_t> remainder;
};

std::optional<WideDivision> DivideWords(const std::vector<uint64_t>& num,
                                        const std::vector<uint64_t>& den,
                                        uint32_t width) {
  if (WordsAreZero(den)) return std::nullopt;
  std::vector<uint64_t> divisor = den;
  divisor.push_back(0);
  std::vector<uint64_t> negated_divisor = divisor;
  NegateWords(negated_divisor);
  WideDivision d{std::vector<uint64_t>(num.size(), 0),
                 std::vector<uint64_t>(num.size() + 1, 0)};
  for (uint32_t bit = width; bit-- > 0;) {
    ShiftInBit(d.remainder, (num[bit / 64] >> (bit % 64)) & 1);
    if (!WordsAtLeast(d.remainder, divisor)) continue;
    AddWords(d.remainder, negated_divisor);
    d.quotient[bit / 64] |= uint64_t{1} << (bit % 64);
  }
  d.remainder.pop_back();
  return d;
}

struct WideOperands {
  std::vector<uint64_t> l;
  std::vector<uint64_t> r;
  bool l_neg;
  bool r_neg;
};

WideOperands ReadOperands(const ConstVal& lhs, const ConstVal& rhs,
                          uint32_t width) {
  bool is_signed = lhs.is_signed && rhs.is_signed;
  WideOperands ops{ExtendedWords(lhs, width, is_signed),
                   ExtendedWords(rhs, width, is_signed), false, false};
  ops.l_neg = is_signed && TopBitSet(ops.l, width);
  ops.r_neg = is_signed && TopBitSet(ops.r, width);
  return ops;
}

void TakeMagnitude(std::vector<uint64_t>& words, uint32_t width,
                   bool negative) {
  if (!negative) return;
  NegateWords(words);
  ClearBitsFrom(words, width);
}

std::optional<std::vector<uint64_t>> WideDivRem(TokenKind op,
                                                const ConstVal& lhs,
                                                const ConstVal& rhs,
                                                uint32_t width) {
  WideOperands ops = ReadOperands(lhs, rhs, width);
  TakeMagnitude(ops.l, width, ops.l_neg);
  TakeMagnitude(ops.r, width, ops.r_neg);
  auto d = DivideWords(ops.l, ops.r, width);
  if (!d) return std::nullopt;
  bool remainder = op == TokenKind::kPercent;
  std::vector<uint64_t> answer =
      remainder ? std::move(d->remainder) : std::move(d->quotient);
  bool negative = remainder ? ops.l_neg : ops.l_neg != ops.r_neg;
  if (negative) NegateWords(answer);
  return answer;
}

std::optional<std::vector<uint64_t>> NegativePower(
    const std::vector<uint64_t>& base, const std::vector<uint64_t>& exponent,
    uint32_t width, bool is_signed) {
  if (WordsAreZero(base)) return std::nullopt;
  std::vector<uint64_t> one = OneInWords(base.size());
  if (base == one) return one;
  std::vector<uint64_t> minus_one = one;
  NegateWords(minus_one);
  ClearBitsFrom(minus_one, width);
  if (is_signed && base == minus_one)
    return (exponent[0] & 1) != 0 ? minus_one : one;
  return std::vector<uint64_t>(base.size(), 0);
}

std::vector<uint64_t> PositivePower(std::vector<uint64_t> base,
                                    const std::vector<uint64_t>& exponent) {
  std::vector<uint64_t> result = OneInWords(base.size());
  for (size_t k = 0; k < exponent.size() * 64; ++k) {
    if (((exponent[k / 64] >> (k % 64)) & 1) != 0)
      result = MultiplyWords(result, base);
    base = MultiplyWords(base, base);
  }
  return result;
}

std::optional<std::vector<uint64_t>> WidePower(const ConstVal& lhs,
                                               const ConstVal& rhs,
                                               uint32_t width) {
  bool is_signed = lhs.is_signed;
  std::vector<uint64_t> base = ExtendedWords(lhs, width, is_signed);
  std::vector<uint64_t> exponent = ExtendedWords(rhs, rhs.width, false);
  bool exp_neg =
      rhs.is_signed && ConstValBit(rhs, static_cast<int64_t>(rhs.width) - 1);
  TakeMagnitude(exponent, rhs.width, exp_neg);
  if (WordsAreZero(exponent)) return OneInWords(base.size());
  if (exp_neg) return NegativePower(base, exponent, width, is_signed);
  return PositivePower(std::move(base), exponent);
}

std::optional<std::vector<uint64_t>> MultiplicativeWords(TokenKind op,
                                                         const ConstVal& lhs,
                                                         const ConstVal& rhs,
                                                         uint32_t width) {
  switch (op) {
    case TokenKind::kStar: {
      WideOperands ops = ReadOperands(lhs, rhs, width);
      return MultiplyWords(ops.l, ops.r);
    }
    case TokenKind::kSlash:
    case TokenKind::kPercent:
      return WideDivRem(op, lhs, rhs, width);
    default:
      return WidePower(lhs, rhs, width);
  }
}

}  // namespace

std::optional<ConstVal> EvalWideMultiplicative(TokenKind op,
                                               const ConstVal& lhs,
                                               const ConstVal& rhs,
                                               uint32_t width) {
  auto words = MultiplicativeWords(op, lhs, rhs, width);
  if (!words) return std::nullopt;
  return ConstValOfWords(*words, width, BinaryResultSigned(op, lhs, rhs));
}

}  // namespace delta
