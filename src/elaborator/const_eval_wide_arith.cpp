// The multiplicative operators over a constant wider than 64 bits. §11.4.3
// (printed pages 275-276 of IEEE 1800-2023) defines the product, the
// quotient, the remainder and the power: the quotient truncates toward zero,
// the remainder takes the sign of the first operand, a division by zero is x,
// and Table 11-4 fixes the power's answer by the signs and sizes of its
// operands, the exponent self-determined. §11.4.3.1 (printed 277) has both
// operands signed read as two's complement values and either unsigned read
// as unsigned, and §11.6.1's Table 11-21 (printed 299-300) sizes a product,
// a quotient and a remainder by the wider operand and a power by its base,
// whose signedness §11.8.1 (printed 302) makes the power's, the exponent
// being self-determined. 994404a79 carried every other operator across
// ConstVal::high_words and left these four on the low word, so `P * 2` over
// a 96-bit P read 0 above bit 64; every power folds here now, whatever its
// width, since the exponent may be wider than the base and the int64 fold
// multiplied once per unit of it.

#include <cstddef>
#include <cstdint>
#include <optional>
#include <utility>
#include <vector>

#include "elaborator/const_eval_internal.h"
#include "lexer/token.h"

namespace delta {
namespace {

// The 32-bit halves of `words`, least significant first, which is what a
// product is worked over so that one half times another fits a uint64_t.
std::vector<uint32_t> HalvesOfWords(const std::vector<uint64_t>& words) {
  std::vector<uint32_t> halves;
  halves.reserve(words.size() * 2);
  for (uint64_t w : words) {
    halves.push_back(static_cast<uint32_t>(w));
    halves.push_back(static_cast<uint32_t>(w >> 32));
  }
  return halves;
}

// §11.4.3: the product of `l` and `r`, both of one word count, cut to that
// count. Schoolbook multiplication over 32-bit halves: each pair of halves'
// product, plus the half already at their place, plus the carry, stays
// below 2^64. The halves above the count are the truncation §11.6.1 gives a
// product evaluated at the width of its operands, and under it the signed
// product is the same bits as the unsigned one, so the operands are read as
// extended words and nothing more.
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

// Whether every bit of `words` is clear.
bool WordsAreZero(const std::vector<uint64_t>& words) {
  for (uint64_t w : words) {
    if (w != 0) return false;
  }
  return true;
}

// Whether `l` is at least `r`, both unsigned values of one word count, read
// from the top word down.
bool WordsAtLeast(const std::vector<uint64_t>& l,
                  const std::vector<uint64_t>& r) {
  for (size_t i = l.size(); i-- > 0;) {
    if (l[i] != r[i]) return l[i] > r[i];
  }
  return true;
}

// Whether bit `width - 1` of `words` is set: the sign of a signed value of
// that width (§11.4.3.1).
bool TopBitSet(const std::vector<uint64_t>& words, uint32_t width) {
  uint32_t top = width - 1;
  return ((words[top / 64] >> (top % 64)) & 1) != 0;
}

// The value 1 in `count` words.
std::vector<uint64_t> OneInWords(size_t count) {
  std::vector<uint64_t> one(count, 0);
  one[0] = 1;
  return one;
}

// `words` shifted up by one bit with `bit` shifted in at the bottom, the
// bit shifted out of the top word dropped.
void ShiftInBit(std::vector<uint64_t>& words, uint64_t bit) {
  uint64_t carry = bit;
  for (uint64_t& w : words) {
    uint64_t top = w >> 63;
    w = (w << 1) | carry;
    carry = top;
  }
}

// The quotient and the remainder of one unsigned division.
struct WideDivision {
  std::vector<uint64_t> quotient;
  std::vector<uint64_t> remainder;
};

// §11.4.3: `num` divided by `den` as unsigned values of `width` bits, by
// long division one bit at a time from the top: the remainder takes each
// bit of the dividend below its own and gives up the divisor wherever it
// holds at least that much, which sets the quotient's bit there. The
// remainder is kept one word longer than the operands so that the bit
// shifted in never carries out of it. Empty for a divisor of zero, which
// §11.4.3 makes the whole result x, as the int64 fold answers it.
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

// The two operands of a multiplicative operator read at `width` as
// §11.4.3.1 reads them: each extended to it from its own sign where both
// are signed and with zeros otherwise, and each one's sign at that width,
// which is clear for an unsigned operand.
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

// The magnitude of the signed value `words` of `width` bits, in place:
// negated where its sign is set, and the bits the negation carried above
// the width cleared, so that the magnitude reads as the unsigned value it
// is.
void TakeMagnitude(std::vector<uint64_t>& words, uint32_t width,
                   bool negative) {
  if (!negative) return;
  NegateWords(words);
  ClearBitsFrom(words, width);
}

// §11.4.3 (printed 275): the quotient, truncated toward zero, or the
// remainder, with the sign of the first operand, of `lhs` by `rhs` at
// `width`. Signed operands divide by their magnitudes and the answer takes
// its sign back: a quotient is negative where exactly one operand is, and a
// remainder where the first is, so `-10 % 3` is -1 and `11 % -3` is 2 as
// Table 11-5 (printed 276) lists them. Empty for a divisor of zero.
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

// Table 11-4's column for a negative exponent, read by the base: 1 for a
// base of 1, 1 or -1 by the exponent's parity for a base of -1, x for a
// base of 0 -- `0 ** -1` being a division by zero, as Table 11-5 notes --
// and 0 for any other base, whose reciprocal truncates to nothing. A base
// is -1 only where the operands are signed, an unsigned base of all ones
// being a large positive number.
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

// Table 11-4's rows for a positive exponent: the base multiplied into 1
// that many times, by squaring, each product cut to the word count and the
// whole cut to the width by the caller.
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

// §11.4.3's Table 11-4 (printed 276): `lhs` to the power `rhs` at `width`.
// The exponent is self-determined, so it is negative by its own signedness
// and sign alone, whatever the base's, and the base is -1 by its own
// signedness alone, whatever the exponent's (§11.8.1); a zero exponent
// answers 1 whatever the base. d6b1cda19 read the base as signed only where
// the exponent was too.
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

// The words of the operator's answer, or empty where §11.4.3 makes it x.
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
