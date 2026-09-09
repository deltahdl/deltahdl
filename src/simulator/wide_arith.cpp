#include "simulator/wide_arith.h"

#include <cstdint>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "lexer/token.h"
#include "simulator/evaluation.h"

namespace delta {
namespace {

// The operands and the result of a wide operation as a little-endian sequence
// of 64-bit limbs, which is the shape Logic4Vec already stores a value in
// (common/types.h) and the shape the school arithmetic below works in.
using Limbs = std::vector<uint64_t>;

uint32_t LimbCount(uint32_t width) { return (width + 63) / 64; }

// Every bit of the top limb that lies inside `width`, so a result can be cut
// back to the width §11.6.1 settled: the arithmetic below carries into bits the
// declaration does not have and none of them may read as set.
uint64_t TopLimbMask(uint32_t width) {
  uint32_t bits = width % 64;
  return bits == 0 ? ~uint64_t{0} : (uint64_t{1} << bits) - 1;
}

void MaskToWidth(Limbs& v, uint32_t width) {
  if (v.empty()) return;
  v.back() &= TopLimbMask(width);
}

// The known bits of a value as limbs, its own width's worth and no more. A
// value whose storage was never masked above its declared width cannot leak
// into the extension below.
Limbs KnownLimbs(const Logic4Vec& v, uint32_t width) {
  Limbs out(LimbCount(width), 0);
  for (uint32_t i = 0; i < out.size() && i < v.nwords; ++i) {
    out[i] = v.words[i].aval & ~v.words[i].bval;
  }
  if (v.width == 0 || v.width >= width) return out;
  uint32_t top = (v.width - 1) / 64;
  if (top >= out.size()) return out;
  out[top] &= TopLimbMask(v.width);
  for (uint32_t i = top + 1; i < out.size(); ++i) out[i] = 0;
  return out;
}

// §11.6.1: a signed operand narrower than the result extends by its sign where
// an unsigned one extends with zeros. The value's own width is where its sign
// bit is, which is not where the result's is.
void SignExtendLimbs(Limbs& v, uint32_t from_width, uint32_t width) {
  if (from_width == 0 || from_width >= width) return;
  uint32_t top = (from_width - 1) / 64;
  if (top >= v.size()) return;
  if (((v[top] >> ((from_width - 1) % 64)) & 1) == 0) return;
  if (from_width % 64 != 0) v[top] |= ~TopLimbMask(from_width);
  for (uint32_t i = top + 1; i < v.size(); ++i) v[i] = ~uint64_t{0};
}

// An operand as the limbs the result width asks for, extended into the bits it
// does not have of its own.
Limbs ToLimbs(const Logic4Vec& v, uint32_t width, bool is_signed) {
  Limbs out = KnownLimbs(v, width);
  if (is_signed) SignExtendLimbs(out, v.width, width);
  MaskToWidth(out, width);
  return out;
}

Logic4Vec FromLimbs(const Limbs& v, uint32_t width, Arena& arena) {
  Logic4Vec out = MakeLogic4Vec(arena, width);
  for (uint32_t i = 0; i < out.nwords; ++i) {
    out.words[i].aval = (i < v.size()) ? v[i] : 0;
    out.words[i].bval = 0;
  }
  return out;
}

// The ripple carry §11.4.3's "a plus b" asks for, across limbs rather than
// within one.
void AddInto(Limbs& a, const Limbs& b) {
  uint64_t carry = 0;
  for (size_t i = 0; i < a.size(); ++i) {
    uint64_t rhs = (i < b.size()) ? b[i] : 0;
    uint64_t sum = a[i] + rhs;
    uint64_t next = (sum < a[i]) ? 1 : 0;
    sum += carry;
    if (carry == 1 && sum == 0) next = 1;
    a[i] = sum;
    carry = next;
  }
}

// Two's complement: the bitwise complement plus one, which is what makes
// subtraction an addition and what carries a negative value's sign into every
// limb above it.
Limbs Negate(const Limbs& v) {
  Limbs out(v.size(), 0);
  for (size_t i = 0; i < v.size(); ++i) out[i] = ~v[i];
  Limbs one(v.size(), 0);
  if (!one.empty()) one[0] = 1;
  AddInto(out, one);
  return out;
}

bool IsZero(const Limbs& v) {
  for (uint64_t limb : v) {
    if (limb != 0) return false;
  }
  return true;
}

bool IsNegative(const Limbs& v, uint32_t width) {
  if (width == 0 || v.empty()) return false;
  return ((v[(width - 1) / 64] >> ((width - 1) % 64)) & 1) != 0;
}

// True when `a` is at least `b`, comparing from the most significant limb down,
// which is the comparison the long division below steps on.
bool AtLeast(const Limbs& a, const Limbs& b) {
  for (size_t i = a.size(); i-- > 0;) {
    uint64_t rhs = (i < b.size()) ? b[i] : 0;
    if (a[i] != rhs) return a[i] > rhs;
  }
  return true;
}

void ShiftLeftOne(Limbs& v) {
  uint64_t carry = 0;
  for (size_t i = 0; i < v.size(); ++i) {
    uint64_t next = v[i] >> 63;
    v[i] = (v[i] << 1) | carry;
    carry = next;
  }
}

void SubInto(Limbs& a, const Limbs& b) { AddInto(a, Negate(b)); }

bool BitAt(const Limbs& v, uint32_t bit) {
  uint32_t limb = bit / 64;
  if (limb >= v.size()) return false;
  return ((v[limb] >> (bit % 64)) & 1) != 0;
}

// A 64-by-64 product as its two halves. The language has no 128-bit integer to
// take it in, so each operand is split at 32 bits and the four partial products
// are recombined -- the same arithmetic a compiler extension would hide.
struct Product64 {
  uint64_t lo = 0;
  uint64_t hi = 0;
};

Product64 Multiply64(uint64_t a, uint64_t b) {
  const uint64_t kLowMask = 0xFFFFFFFFull;
  uint64_t a_lo = a & kLowMask;
  uint64_t a_hi = a >> 32;
  uint64_t b_lo = b & kLowMask;
  uint64_t b_hi = b >> 32;
  uint64_t lo_lo = a_lo * b_lo;
  uint64_t lo_hi = a_lo * b_hi;
  uint64_t hi_lo = a_hi * b_lo;
  uint64_t hi_hi = a_hi * b_hi;
  uint64_t cross = (lo_lo >> 32) + (lo_hi & kLowMask) + (hi_lo & kLowMask);
  Product64 out;
  out.lo = (lo_lo & kLowMask) | (cross << 32);
  out.hi = hi_hi + (lo_hi >> 32) + (hi_lo >> 32) + (cross >> 32);
  return out;
}

// The schoolbook product: every partial product placed at its own limb with the
// half that does not fit carried into the next. Partial products whose place
// lies above the result width are dropped, which is the truncation §11.6.1
// already applies to the width.
Limbs Multiply(const Limbs& a, const Limbs& b) {
  Limbs out(a.size(), 0);
  for (size_t i = 0; i < a.size(); ++i) {
    uint64_t carry = 0;
    for (size_t j = 0; i + j < out.size(); ++j) {
      uint64_t rhs = (j < b.size()) ? b[j] : 0;
      Product64 p = Multiply64(a[i], rhs);
      uint64_t sum = out[i + j] + p.lo;
      uint64_t carry_lo = (sum < p.lo) ? 1 : 0;
      uint64_t sum_with_carry = sum + carry;
      uint64_t carry_in = (sum_with_carry < carry) ? 1 : 0;
      out[i + j] = sum_with_carry;
      carry = p.hi + carry_lo + carry_in;
    }
  }
  return out;
}

// Binary long division: one shift and one conditional subtraction per bit of
// the dividend, which needs no estimate of a quotient digit and so no case
// analysis to get wrong. `width` bits is a bounded number of steps -- 128 for
// the widths a declaration reaches in practice.
struct DivResult {
  Limbs quotient;
  Limbs remainder;
};

DivResult DivMod(const Limbs& dividend, const Limbs& divisor, uint32_t width) {
  DivResult out{Limbs(dividend.size(), 0), Limbs(dividend.size(), 0)};
  for (uint32_t bit = width; bit-- > 0;) {
    ShiftLeftOne(out.remainder);
    if (BitAt(dividend, bit)) out.remainder[0] |= 1;
    if (AtLeast(out.remainder, divisor)) {
      SubInto(out.remainder, divisor);
      out.quotient[bit / 64] |= uint64_t{1} << (bit % 64);
    }
  }
  return out;
}

// §11.4.3: "The result of the power operator is the base raised to the power of
// the exponent", taken here by squaring so the number of multiplications
// follows the exponent's bit count rather than its value. Every product is
// already truncated to the result width by Multiply.
Limbs Power(const Limbs& base, const Limbs& exp, uint32_t width) {
  Limbs result(base.size(), 0);
  if (!result.empty()) result[0] = 1;
  MaskToWidth(result, width);
  Limbs acc = base;
  for (uint32_t bit = 0; bit < width; ++bit) {
    if (BitAt(exp, bit)) {
      result = Multiply(result, acc);
      MaskToWidth(result, width);
    }
    acc = Multiply(acc, acc);
    MaskToWidth(acc, width);
  }
  return result;
}

// §11.4.3 gives division a quotient truncated toward zero and gives the
// modulus the sign of the first operand, so both are taken on magnitudes and
// the sign is applied afterwards.
struct SignedDivision {
  Limbs magnitude;
  bool negative = false;
};

SignedDivision DivideMagnitudes(const Limbs& lhs, const Limbs& rhs,
                                const WideArithSpec& spec,
                                bool want_remainder) {
  bool lhs_neg = spec.is_signed && IsNegative(lhs, spec.width);
  bool rhs_neg = spec.is_signed && IsNegative(rhs, spec.width);
  Limbs a = lhs_neg ? Negate(lhs) : lhs;
  Limbs b = rhs_neg ? Negate(rhs) : rhs;
  MaskToWidth(a, spec.width);
  MaskToWidth(b, spec.width);
  DivResult dr = DivMod(a, b, spec.width);
  if (want_remainder) return {dr.remainder, lhs_neg};
  return {dr.quotient, lhs_neg != rhs_neg};
}

Limbs ApplySign(const SignedDivision& d, uint32_t width) {
  Limbs out = d.negative ? Negate(d.magnitude) : d.magnitude;
  MaskToWidth(out, width);
  return out;
}

// §11.4.4's answer for a negative exponent, which the squaring above cannot
// take: 1 where the base is 1, the base itself where it is -1 and the exponent
// odd, and 0 for every other base.
Limbs NegativeExponentResult(const Limbs& base, const Limbs& exp,
                             uint32_t width) {
  Limbs one(base.size(), 0);
  if (!one.empty()) one[0] = 1;
  MaskToWidth(one, width);
  Limbs minus_one = Negate(one);
  MaskToWidth(minus_one, width);
  if (base == one) return one;
  if (base == minus_one) return BitAt(exp, 0) ? minus_one : one;
  return Limbs(base.size(), 0);
}

}  // namespace

Logic4Vec EvalWideArith(TokenKind op, const Logic4Vec& lhs,
                        const Logic4Vec& rhs, const WideArithSpec& spec,
                        Arena& arena) {
  Limbs a = ToLimbs(lhs, spec.width, spec.is_signed);
  Limbs b = ToLimbs(rhs, spec.width, spec.is_signed);
  Limbs result(a.size(), 0);
  switch (op) {
    case TokenKind::kPlus:
      result = a;
      AddInto(result, b);
      break;
    case TokenKind::kMinus:
      result = a;
      SubInto(result, b);
      break;
    case TokenKind::kStar:
      result = Multiply(a, b);
      break;
    case TokenKind::kSlash:
    case TokenKind::kPercent:
      // §11.4.3: "Division or modulus by zero shall produce a result with all
      // bits set to x."
      if (IsZero(b)) return MakeAllX(arena, spec.width);
      result = ApplySign(
          DivideMagnitudes(a, b, spec, op == TokenKind::kPercent), spec.width);
      break;
    case TokenKind::kPower:
      // §11.4.4: with an integer base and a negative exponent the result is 0,
      // except that a base of 1 gives 1 and a base of -1 gives 1 or -1 by the
      // exponent's parity. The squaring below reads the exponent's bits as a
      // magnitude, which a negative exponent is not.
      if (spec.is_signed && IsNegative(b, spec.width)) {
        result = NegativeExponentResult(a, b, spec.width);
        break;
      }
      result = Power(a, b, spec.width);
      break;
    default:
      break;
  }
  MaskToWidth(result, spec.width);
  Logic4Vec out = FromLimbs(result, spec.width, arena);
  out.is_signed = spec.is_signed;
  return out;
}

}  // namespace delta
