#include "simulator/wide_arith.h"

#include <cstddef>
#include <cstdint>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "lexer/token.h"
#include "simulator/evaluation.h"

namespace delta {
namespace {

using Limbs = std::vector<uint64_t>;

uint32_t LimbCount(uint32_t width) { return (width + 63) / 64; }

uint64_t TopLimbMask(uint32_t width) {
  uint32_t bits = width % 64;
  return bits == 0 ? ~uint64_t{0} : (uint64_t{1} << bits) - 1;
}

void MaskToWidth(Limbs& v, uint32_t width) { v.back() &= TopLimbMask(width); }

Limbs KnownLimbs(const Logic4Vec& v, uint32_t width) {
  Limbs out(LimbCount(width), 0);
  for (uint32_t i = 0; i < out.size() && i < v.nwords; ++i) {
    uint64_t own = (i + 1 == v.nwords) ? TopLimbMask(v.width) : ~uint64_t{0};
    out[i] = v.words[i].aval & ~v.words[i].bval & own;
  }
  return out;
}

bool BitAt(const Limbs& v, uint32_t bit) {
  return ((v[bit / 64] >> (bit % 64)) & 1) != 0;
}

void SignExtendLimbs(Limbs& v, uint32_t from_width, uint32_t width) {
  if (from_width >= width || !BitAt(v, from_width - 1)) return;
  for (uint32_t bit = from_width; bit < width; ++bit)
    v[bit / 64] |= uint64_t{1} << (bit % 64);
}

Limbs ToLimbs(const Logic4Vec& v, uint32_t width, bool is_signed) {
  Limbs out = KnownLimbs(v, width);
  if (is_signed) SignExtendLimbs(out, v.width, width);
  MaskToWidth(out, width);
  return out;
}

Logic4Vec FromLimbs(const Limbs& v, uint32_t width, Arena& arena) {
  Logic4Vec out = MakeLogic4Vec(arena, width);
  for (uint32_t i = 0; i < out.nwords; ++i) {
    out.words[i].aval = v[i];
    out.words[i].bval = 0;
  }
  return out;
}

void AddInto(Limbs& a, const Limbs& b) {
  uint64_t carry = 0;
  for (size_t i = 0; i < a.size(); ++i) {
    uint64_t sum = a[i] + b[i];
    uint64_t next = (sum < a[i]) ? 1 : 0;
    sum += carry;
    if (carry == 1 && sum == 0) next = 1;
    a[i] = sum;
    carry = next;
  }
}

Limbs Negate(const Limbs& v) {
  Limbs out(v.size(), 0);
  for (size_t i = 0; i < v.size(); ++i) out[i] = ~v[i];
  Limbs one(v.size(), 0);
  one[0] = 1;
  AddInto(out, one);
  return out;
}

bool IsZero(const Limbs& v) {
  for (uint64_t limb : v) {
    if (limb != 0) return false;
  }
  return true;
}

bool IsNegative(const Limbs& v, uint32_t width) { return BitAt(v, width - 1); }

bool AtLeast(const Limbs& a, const Limbs& b) {
  for (size_t i = a.size(); i-- > 0;) {
    if (a[i] != b[i]) return a[i] > b[i];
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

Limbs Multiply(const Limbs& a, const Limbs& b) {
  Limbs out(a.size(), 0);
  for (size_t i = 0; i < a.size(); ++i) {
    uint64_t carry = 0;
    for (size_t j = 0; i + j < out.size(); ++j) {
      Product64 p = Multiply64(a[i], b[j]);
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

Limbs Power(const Limbs& base, const Limbs& exp, uint32_t width) {
  Limbs result(base.size(), 0);
  result[0] = 1;
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

Limbs NegativeExponentResult(const Limbs& base, const Limbs& exp,
                             uint32_t width) {
  Limbs one(base.size(), 0);
  one[0] = 1;
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
      if (IsZero(b)) return MakeAllX(arena, spec.width);
      result = ApplySign(
          DivideMagnitudes(a, b, spec, op == TokenKind::kPercent), spec.width);
      break;
    default:
      b = ToLimbs(rhs, spec.width, spec.exponent_is_signed);
      if (spec.exponent_is_signed && IsNegative(b, spec.width)) {
        if (IsZero(a)) return MakeAllX(arena, spec.width);
        result = NegativeExponentResult(a, b, spec.width);
        break;
      }
      result = Power(a, b, spec.width);
      break;
  }
  MaskToWidth(result, spec.width);
  Logic4Vec out = FromLimbs(result, spec.width, arena);
  out.is_signed = spec.is_signed;
  return out;
}

}  // namespace delta
