#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <string>

#include "common/arena.h"
#include "common/types.h"
#include "lexer/token.h"
#include "simulator/assoc_index.h"
#include "simulator/evaluation.h"
#include "simulator/evaluation_internal.h"
#include "simulator/wide_arith.h"

namespace delta {

static Logic4Word ExtractBit(const Logic4Vec& v, uint32_t idx) {
  uint32_t word = idx / 64;
  uint64_t mask = uint64_t{1} << (idx % 64);
  uint64_t a = (v.words[word].aval & mask) ? 1 : 0;
  uint64_t b = (v.words[word].bval & mask) ? 1 : 0;
  return {a, b};
}

using FoldFn = Logic4Word (*)(Logic4Word, Logic4Word);
static FoldFn ReductionFoldFn(TokenKind op) {
  switch (op) {
    case TokenKind::kAmp:
    case TokenKind::kTildeAmp:
      return Logic4And;
    case TokenKind::kPipe:
    case TokenKind::kTildePipe:
      return Logic4Or;
    default:
      return Logic4Xor;
  }
}
static Logic4Vec EvalReductionOp(TokenKind op, Logic4Vec operand,
                                 Arena& arena) {
  if (operand.width == 0) return MakeLogic4Vec(arena, 1);
  auto fold = ReductionFoldFn(op);
  Logic4Word acc = ExtractBit(operand, 0);
  for (uint32_t i = 1; i < operand.width; ++i) {
    acc = fold(acc, ExtractBit(operand, i));
  }
  bool negate = op == TokenKind::kTildeAmp || op == TokenKind::kTildePipe ||
                op == TokenKind::kTildeCaret || op == TokenKind::kCaretTilde;
  if (negate) {
    acc = Logic4Not(acc);
    acc.aval &= 1;
    acc.bval &= 1;
  }
  auto result = MakeLogic4Vec(arena, 1);
  result.words[0] = acc;
  return result;
}
static bool IsReductionOp(TokenKind op) {
  switch (op) {
    case TokenKind::kAmp:
    case TokenKind::kPipe:
    case TokenKind::kCaret:
    case TokenKind::kTildeAmp:
    case TokenKind::kTildePipe:
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
      return true;
    default:
      return false;
  }
}
static Logic4Vec EvalUnaryNot(Logic4Vec operand, Arena& arena) {
  auto result = MakeLogic4Vec(arena, operand.width);
  for (uint32_t i = 0; i < result.nwords; ++i) {
    result.words[i] = Logic4Not(operand.words[i]);
  }

  uint32_t bit_pos = operand.width % 64;
  if (bit_pos != 0) {
    uint64_t mask = (uint64_t{1} << bit_pos) - 1;
    result.words[result.nwords - 1].aval &= mask;
    result.words[result.nwords - 1].bval &= mask;
  }
  result.is_signed = operand.is_signed;
  return result;
}

static Logic4Vec EvalUnaryMinus(Logic4Vec operand, Arena& arena) {
  if (operand.is_real) {
    return MakeRealVec(arena, -RealVecToDouble(operand), operand.width);
  }
  if (HasUnknownBits(operand)) return MakeAllX(arena, operand.width);
  auto r = MakeLogic4Vec(arena, operand.width);
  uint64_t carry = 1;
  for (uint32_t i = 0; i < r.nwords; ++i) {
    uint64_t inverted = ~operand.words[i].aval;
    uint64_t sum = inverted + carry;
    carry = sum < inverted ? 1 : 0;
    r.words[i].aval = sum & WordMaskWithinWidth(operand.width, i);
  }
  r.is_signed = operand.is_signed;
  return r;
}

Logic4Vec EvalUnaryOp(TokenKind op, Logic4Vec operand, Arena& arena) {
  if (operand.nwords == 0) return operand;
  if (IsReductionOp(op)) return EvalReductionOp(op, operand, arena);
  switch (op) {
    case TokenKind::kTilde:
      return EvalUnaryNot(operand, arena);
    case TokenKind::kBang: {
      const Truth kTruth = TruthOf(operand);
      if (kTruth == Truth::kAmbiguous) return MakeAllX(arena, 1);
      return TruthBit(kTruth == Truth::kTrue ? Truth::kFalse : Truth::kTrue,
                      arena);
    }
    case TokenKind::kMinus:
      return EvalUnaryMinus(operand, arena);
    case TokenKind::kPlus:
      if (!operand.is_real && HasUnknownBits(operand))
        return MakeAllX(arena, operand.width);
      return operand;
    default:
      return operand;
  }
}
static uint64_t IntPow(uint64_t base, uint64_t exp) {
  uint64_t result = 1;
  while (exp > 0) {
    if (exp & 1) result *= base;
    base *= base;
    exp >>= 1;
  }
  return result;
}

static Logic4Vec EvalIntegralPower(const Logic4Vec& lhs, const Logic4Vec& rhs,
                                   uint32_t width, Arena& arena) {
  const int64_t kBase = lhs.is_signed ? SignExtend(lhs.ToUint64(), lhs.width)
                                      : static_cast<int64_t>(lhs.ToUint64());
  const int64_t kExp = rhs.is_signed ? SignExtend(rhs.ToUint64(), rhs.width)
                                     : static_cast<int64_t>(rhs.ToUint64());
  uint64_t r = 0;
  if (rhs.is_signed && kExp < 0) {
    if (kBase == 0) {
      Logic4Vec x = MakeAllX(arena, width);
      x.is_signed = lhs.is_signed;
      return x;
    }
    if (kBase == 1) r = 1;
    if (lhs.is_signed && kBase == -1)
      r = static_cast<uint64_t>(kExp % 2 == 0 ? 1 : -1);
  } else {
    r = IntPow(static_cast<uint64_t>(kBase), static_cast<uint64_t>(kExp));
  }
  Logic4Vec result = MakeLogic4VecVal(arena, width, r);
  result.is_signed = lhs.is_signed;
  return result;
}
static Logic4Vec EvalPower(const Logic4Vec& lhs, const Logic4Vec& rhs,
                           uint32_t width, Arena& arena) {
  if (width > 64) {
    return EvalWideArith(TokenKind::kPower, lhs, rhs,
                         {width, lhs.is_signed, rhs.is_signed}, arena);
  }
  return EvalIntegralPower(lhs, rhs, width, arena);
}

static Logic4Vec EvalSignedArith(TokenKind op, Logic4Vec lhs, Logic4Vec rhs,
                                 uint32_t width, Arena& arena) {
  int64_t lv = SignExtend(lhs.ToUint64(), lhs.width);
  int64_t rv = SignExtend(rhs.ToUint64(), rhs.width);
  int64_t r = 0;
  switch (op) {
    case TokenKind::kPlus:
      r = lv + rv;
      break;
    case TokenKind::kMinus:
      r = lv - rv;
      break;
    case TokenKind::kStar:
      r = lv * rv;
      break;
    case TokenKind::kSlash:
      if (rv == 0) return MakeAllX(arena, width);
      r = rv == -1 ? static_cast<int64_t>(-static_cast<uint64_t>(lv)) : lv / rv;
      break;
    case TokenKind::kPercent:
      if (rv == 0) return MakeAllX(arena, width);
      r = rv == -1 ? 0 : lv % rv;
      break;
    default:
      break;
  }
  auto result = MakeLogic4VecVal(arena, width, static_cast<uint64_t>(r));
  result.is_signed = true;
  return result;
}

double RealVecToDouble(const Logic4Vec& v) {
  if (v.width == 32) {
    float f = 0.0f;
    auto bits = static_cast<uint32_t>(v.ToUint64());
    std::memcpy(&f, &bits, sizeof(float));
    return static_cast<double>(f);
  }
  double d = 0.0;
  uint64_t bits = v.ToUint64();
  std::memcpy(&d, &bits, sizeof(double));
  return d;
}

double RealValueOf(const Logic4Vec& v) {
  if (v.is_real) return RealVecToDouble(v);
  if (v.is_signed && v.width <= 64)
    return static_cast<double>(SignExtend(v.ToUint64(), v.width));
  return static_cast<double>(v.ToUint64());
}

Logic4Vec MakeRealVec(Arena& arena, double val, uint32_t width) {
  if (width == 32) {
    auto f = static_cast<float>(val);
    uint32_t bits = 0;
    std::memcpy(&bits, &f, sizeof(float));
    auto r = MakeLogic4VecVal(arena, 32, bits);
    r.is_real = true;
    return r;
  }
  uint64_t bits = 0;
  std::memcpy(&bits, &val, sizeof(double));
  auto r = MakeLogic4VecVal(arena, 64, bits);
  r.is_real = true;
  return r;
}

static uint32_t RealResultWidth(const Logic4Vec& lhs, const Logic4Vec& rhs) {
  bool lhs_real64 = lhs.is_real && lhs.width == 64;
  bool rhs_real64 = rhs.is_real && rhs.width == 64;
  if (lhs_real64 || rhs_real64) return 64;
  return 32;
}

static Logic4Vec EvalRealArith(TokenKind op, const Logic4Vec& lhs,
                               const Logic4Vec& rhs, Arena& arena) {
  double lv = RealValueOf(lhs);
  double rv = RealValueOf(rhs);
  uint32_t w = RealResultWidth(lhs, rhs);
  switch (op) {
    case TokenKind::kPlus:
      return MakeRealVec(arena, lv + rv, w);
    case TokenKind::kMinus:
      return MakeRealVec(arena, lv - rv, w);
    case TokenKind::kStar:
      return MakeRealVec(arena, lv * rv, w);
    case TokenKind::kSlash:
      if (rv == 0.0) return MakeAllX(arena, w);
      return MakeRealVec(arena, lv / rv, w);
    case TokenKind::kPower:
      return MakeRealVec(arena, std::pow(lv, rv), w);
    default:
      return MakeRealVec(arena, 0.0, w);
  }
}
static Logic4Vec EvalUnsignedArith(TokenKind op, Logic4Vec lhs, Logic4Vec rhs,
                                   uint32_t width, Arena& arena) {
  uint64_t lv = lhs.ToUint64();
  uint64_t rv = rhs.ToUint64();
  uint64_t result = 0;
  switch (op) {
    case TokenKind::kPlus:
      result = lv + rv;
      break;
    case TokenKind::kMinus:
      result = lv - rv;
      break;
    case TokenKind::kStar:
      result = lv * rv;
      break;
    case TokenKind::kSlash:
      if (rv == 0) return MakeAllX(arena, width);
      result = lv / rv;
      break;
    case TokenKind::kPercent:
      if (rv == 0) return MakeAllX(arena, width);
      result = lv % rv;
      break;
    default:
      break;
  }
  return MakeLogic4VecVal(arena, width, result);
}

static Logic4Vec EvalBinaryArith(TokenKind op, Logic4Vec lhs, Logic4Vec rhs,
                                 Arena& arena, uint32_t context_width = 0) {
  if (lhs.is_real || rhs.is_real) return EvalRealArith(op, lhs, rhs, arena);
  uint32_t self_w = (op == TokenKind::kPower)
                        ? lhs.width
                        : ((lhs.width > rhs.width) ? lhs.width : rhs.width);
  uint32_t width = (context_width > self_w) ? context_width : self_w;
  if (HasUnknownBits(lhs) || HasUnknownBits(rhs)) {
    auto result = MakeAllX(arena, width);
    result.is_signed = lhs.is_signed && rhs.is_signed;
    return result;
  }

  if (op == TokenKind::kPower) return EvalPower(lhs, rhs, width, arena);
  if (width > 64) {
    return EvalWideArith(op, lhs, rhs, {width, lhs.is_signed && rhs.is_signed},
                         arena);
  }
  if (lhs.is_signed && rhs.is_signed) {
    return EvalSignedArith(op, lhs, rhs, width, arena);
  }
  return EvalUnsignedArith(op, lhs, rhs, width, arena);
}
static Logic4Vec EvalBinaryBitwise(TokenKind op, Logic4Vec lhs, Logic4Vec rhs,
                                   Arena& arena, uint32_t context_width = 0) {
  uint32_t self_w = (lhs.width > rhs.width) ? lhs.width : rhs.width;
  uint32_t width = (context_width > self_w) ? context_width : self_w;

  bool sign_ext = lhs.is_signed && rhs.is_signed;
  if (lhs.width < width) lhs = ExtendVec(lhs, width, sign_ext, arena);
  if (rhs.width < width) rhs = ExtendVec(rhs, width, sign_ext, arena);
  auto result = MakeLogic4Vec(arena, width);
  uint32_t words = result.nwords;
  for (uint32_t i = 0; i < words; ++i) {
    auto lw = lhs.words[i];
    auto rw = rhs.words[i];
    switch (op) {
      case TokenKind::kAmp:
        result.words[i] = Logic4And(lw, rw);
        break;
      case TokenKind::kPipe:
        result.words[i] = Logic4Or(lw, rw);
        break;
      case TokenKind::kCaret:
        result.words[i] = Logic4Xor(lw, rw);
        break;
      case TokenKind::kTildeCaret:
      case TokenKind::kCaretTilde:
        result.words[i] = Logic4Not(Logic4Xor(lw, rw));
        break;
      default:
        break;
    }
  }
  result.is_signed = lhs.is_signed && rhs.is_signed;

  bool is_xnor = op == TokenKind::kTildeCaret || op == TokenKind::kCaretTilde;
  uint32_t bit_pos = width % 64;
  if (is_xnor && bit_pos != 0) {
    uint64_t mask = (uint64_t{1} << bit_pos) - 1;
    result.words[words - 1].aval &= mask;
    result.words[words - 1].bval &= mask;
  }
  return result;
}
static void ApplySignFill(Logic4Vec& result, const Logic4Vec& v,
                          uint32_t target_width) {
  uint32_t msb_idx = (v.width - 1) / 64;
  uint64_t msb_mask = uint64_t{1} << ((v.width - 1) % 64);
  uint64_t a_fill = (v.words[msb_idx].aval & msb_mask) ? ~uint64_t{0} : 0;
  uint64_t b_fill = (v.words[msb_idx].bval & msb_mask) ? ~uint64_t{0} : 0;
  if (!(a_fill || b_fill)) return;
  uint32_t fill_bit = v.width % 64;
  if (fill_bit != 0) {
    uint64_t mask = ~((uint64_t{1} << fill_bit) - 1);
    result.words[v.width / 64].aval |= a_fill & mask;
    result.words[v.width / 64].bval |= b_fill & mask;
  }
  uint32_t first_full = v.width / 64 + (fill_bit != 0 ? 1 : 0);
  for (uint32_t i = first_full; i < result.nwords; ++i) {
    result.words[i].aval = a_fill;
    result.words[i].bval = b_fill;
  }
  uint32_t top_bit = target_width % 64;
  if (top_bit != 0 && result.nwords > 0) {
    uint64_t top_mask = (uint64_t{1} << top_bit) - 1;
    result.words[result.nwords - 1].aval &= top_mask;
    result.words[result.nwords - 1].bval &= top_mask;
  }
}

Logic4Vec ExtendVec(const Logic4Vec& v, uint32_t target_width, bool sign_ext,
                    Arena& arena) {
  if (v.fills_width && target_width > v.width)
    return FillUnbasedUnsized(v, target_width, arena);
  auto result = MakeLogic4Vec(arena, target_width);
  for (uint32_t i = 0; i < v.nwords; ++i) {
    result.words[i] = v.words[i];
  }
  if (sign_ext && v.width > 0) {
    ApplySignFill(result, v, target_width);
  }
  result.is_signed = v.is_signed;
  result.is_real = v.is_real;
  result.is_string = v.is_string;
  return result;
}
bool EvalCaseEquality(Logic4Vec lhs, Logic4Vec rhs) {
  if (lhs.width != rhs.width) return false;
  for (uint32_t i = 0; i < lhs.nwords; ++i) {
    if (lhs.words[i].aval != rhs.words[i].aval) return false;
    if (lhs.words[i].bval != rhs.words[i].bval) return false;
  }
  return true;
}

struct ShiftPlane {
  const Logic4Vec* src = nullptr;
  bool bval = false;
  uint64_t fill = 0;
};

static uint64_t ShiftPlaneWord(const ShiftPlane& p, int64_t index) {
  if (index < 0) return 0;
  if (index >= static_cast<int64_t>(p.src->nwords)) return p.fill;
  const Logic4Word& w = p.src->words[index];
  uint64_t bits = p.bval ? w.bval : w.aval;
  uint64_t mask =
      WordMaskWithinWidth(p.src->width, static_cast<uint32_t>(index));
  return (bits & mask) | (p.fill & ~mask);
}

static uint64_t ShiftedPlaneWord(const ShiftPlane& p, uint32_t index,
                                 uint64_t count, bool left) {
  auto word_shift = static_cast<int64_t>(count / 64);
  auto bit_shift = static_cast<uint32_t>(count % 64);
  auto i = static_cast<int64_t>(index);
  if (left) {
    uint64_t hi = ShiftPlaneWord(p, i - word_shift) << bit_shift;
    if (bit_shift == 0) return hi;
    return hi | (ShiftPlaneWord(p, i - word_shift - 1) >> (64 - bit_shift));
  }
  uint64_t lo = ShiftPlaneWord(p, i + word_shift) >> bit_shift;
  if (bit_shift == 0) return lo;
  return lo | (ShiftPlaneWord(p, i + word_shift + 1) << (64 - bit_shift));
}

static uint64_t PlaneSignFill(const Logic4Vec& v, bool bval) {
  if (v.width == 0) return 0;
  uint32_t top = v.width - 1;
  const Logic4Word& w = v.words[top / 64];
  uint64_t bits = bval ? w.bval : w.aval;
  return ((bits >> (top % 64)) & 1) ? ~uint64_t{0} : 0;
}

static Logic4Vec EvalShift(TokenKind op, Logic4Vec lhs, uint64_t count,
                           Arena& arena) {
  bool left = op == TokenKind::kLtLt || op == TokenKind::kLtLtLt;
  bool sign_fill = op == TokenKind::kGtGtGt && lhs.is_signed;
  if (count > lhs.width) count = lhs.width;
  auto result = MakeLogic4Vec(arena, lhs.width);
  result.is_signed = lhs.is_signed;
  ShiftPlane a{&lhs, false, sign_fill ? PlaneSignFill(lhs, false) : 0};
  ShiftPlane b{&lhs, true, sign_fill ? PlaneSignFill(lhs, true) : 0};
  for (uint32_t i = 0; i < result.nwords; ++i) {
    uint64_t mask = WordMaskWithinWidth(lhs.width, i);
    result.words[i].aval = ShiftedPlaneWord(a, i, count, left) & mask;
    result.words[i].bval = ShiftedPlaneWord(b, i, count, left) & mask;
  }
  return result;
}

static uint64_t ShiftCount(const Logic4Vec& rhs) {
  for (uint32_t i = 1; i < rhs.nwords; ++i) {
    if (rhs.words[i].aval != 0) return ~uint64_t{0};
  }
  return rhs.ToUint64();
}

static constexpr uint64_t kResultX = 2;
static uint64_t EvalWildcardEq(Logic4Vec lhs, Logic4Vec rhs) {
  uint32_t nwords = std::min(lhs.nwords, rhs.nwords);
  bool unknown = false;
  for (uint32_t i = 0; i < nwords; ++i) {
    uint64_t compared = ~rhs.words[i].bval;
    uint64_t known = compared & ~lhs.words[i].bval;
    if (((lhs.words[i].aval ^ rhs.words[i].aval) & known) != 0) return 0;
    unknown = unknown || (lhs.words[i].bval & compared) != 0;
  }
  return unknown ? kResultX : 1;
}
static uint64_t EvalLogicalEq(const Logic4Vec& lhs, const Logic4Vec& rhs) {
  uint32_t nwords = std::min(lhs.nwords, rhs.nwords);
  bool unknown = false;
  for (uint32_t i = 0; i < nwords; ++i) {
    uint64_t known = ~(lhs.words[i].bval | rhs.words[i].bval);
    if (((lhs.words[i].aval ^ rhs.words[i].aval) & known) != 0) return 0;
    unknown = unknown || ~known != 0;
  }
  return unknown ? kResultX : 1;
}
static uint64_t EvalEqualityOp(TokenKind op, Logic4Vec lhs, Logic4Vec rhs) {
  switch (op) {
    case TokenKind::kEqEq:
      return EvalLogicalEq(lhs, rhs);
    case TokenKind::kBangEq: {
      uint64_t r = EvalLogicalEq(lhs, rhs);
      return r == kResultX ? kResultX : r ^ 1;
    }
    case TokenKind::kEqEqEq:
      return EvalCaseEquality(lhs, rhs) ? 1 : 0;
    case TokenKind::kBangEqEq:
      return EvalCaseEquality(lhs, rhs) ? 0 : 1;
    case TokenKind::kEqEqQuestion:
      return EvalWildcardEq(lhs, rhs);
    case TokenKind::kBangEqQuestion: {
      uint64_t r = EvalWildcardEq(lhs, rhs);
      return r == kResultX ? kResultX : r ^ 1;
    }
    default:
      return 0;
  }
}
Truth TruthOf(const Logic4Vec& v) {
  if (v.is_real)
    return RealVecToDouble(v) != 0.0 ? Truth::kTrue : Truth::kFalse;
  bool ambiguous = false;
  for (uint32_t i = 0; i < v.nwords; ++i) {
    if ((v.words[i].aval & ~v.words[i].bval) != 0) return Truth::kTrue;
    ambiguous = ambiguous || v.words[i].bval != 0;
  }
  return ambiguous ? Truth::kAmbiguous : Truth::kFalse;
}

Logic4Vec TruthBit(Truth t, Arena& arena) {
  if (t == Truth::kAmbiguous) return MakeAllX(arena, 1);
  return MakeLogic4VecVal(arena, 1, t == Truth::kTrue ? 1 : 0);
}

int64_t SignExtend(uint64_t val, uint32_t width) {
  if (width == 0 || width >= 64) return static_cast<int64_t>(val);
  uint64_t mask = uint64_t{1} << (width - 1);
  return static_cast<int64_t>((val ^ mask) - mask);
}

AssocIndex AssocIntKey(const Logic4Vec& val, bool is_wildcard,
                       uint32_t index_width, bool is_signed) {
  return AssocIndex::Of(val, is_wildcard, index_width, is_signed);
}

std::string AssocStringKey(const Logic4Vec& val) {
  uint32_t nb = val.width / 8;
  std::string s;
  s.reserve(nb);
  for (uint32_t i = nb; i > 0; --i) {
    uint32_t bi = i - 1;
    auto ch = static_cast<char>(
        (val.words[(bi * 8) / 64].aval >> ((bi * 8) % 64)) & 0xFF);
    if (ch != 0) s.push_back(ch);
  }
  return s;
}

static int CompareIntegral(Logic4Vec lhs, Logic4Vec rhs, Arena& arena) {
  const uint32_t kWidth = std::max(lhs.width, rhs.width);
  const bool kSigned = lhs.is_signed && rhs.is_signed;
  if (lhs.width < kWidth) lhs = ExtendVec(lhs, kWidth, kSigned, arena);
  if (rhs.width < kWidth) rhs = ExtendVec(rhs, kWidth, kSigned, arena);
  if (kSigned) {
    const uint32_t kTop = kWidth - 1;
    const bool kLhsNegative = (lhs.words[kTop / 64].aval >> (kTop % 64)) & 1;
    const bool kRhsNegative = (rhs.words[kTop / 64].aval >> (kTop % 64)) & 1;
    if (kLhsNegative != kRhsNegative) return kLhsNegative ? -1 : 1;
  }
  for (uint32_t i = lhs.nwords; i > 0; --i) {
    const uint64_t kL = lhs.words[i - 1].aval;
    const uint64_t kR = rhs.words[i - 1].aval;
    if (kL != kR) return kL < kR ? -1 : 1;
  }
  return 0;
}

static bool IsEqualityOp(TokenKind op) {
  return op == TokenKind::kEqEq || op == TokenKind::kEqEqEq ||
         op == TokenKind::kBangEq || op == TokenKind::kBangEqEq ||
         op == TokenKind::kEqEqQuestion || op == TokenKind::kBangEqQuestion;
}

static Logic4Vec EvalRealRelational(TokenKind op, const Logic4Vec& lhs,
                                    const Logic4Vec& rhs, Arena& arena) {
  double ld = RealValueOf(lhs);
  double rd = RealValueOf(rhs);
  bool r = false;
  switch (op) {
    case TokenKind::kLt:
      r = ld < rd;
      break;
    case TokenKind::kGt:
      r = ld > rd;
      break;
    case TokenKind::kLtEq:
      r = ld <= rd;
      break;
    case TokenKind::kGtEq:
      r = ld >= rd;
      break;
    default:
      break;
  }
  return MakeLogic4VecVal(arena, 1, r ? 1 : 0);
}

static Logic4Vec EvalRelational(TokenKind op, Logic4Vec lhs, Logic4Vec rhs,
                                Arena& arena) {
  if (lhs.is_real || rhs.is_real) {
    return EvalRealRelational(op, lhs, rhs, arena);
  }
  if (HasUnknownBits(lhs) || HasUnknownBits(rhs)) {
    return MakeAllX(arena, 1);
  }
  const int kOrder = CompareIntegral(lhs, rhs, arena);
  bool holds = kOrder >= 0;
  if (op == TokenKind::kLt) holds = kOrder < 0;
  if (op == TokenKind::kGt) holds = kOrder > 0;
  if (op == TokenKind::kLtEq) holds = kOrder <= 0;
  return MakeLogic4VecVal(arena, 1, holds ? 1 : 0);
}

static std::string PackedToStr(const Logic4Vec& vec) {
  std::string result;
  uint32_t nbytes = vec.width / 8;
  result.reserve(nbytes);
  for (uint32_t i = nbytes; i > 0; --i) {
    uint32_t byte_idx = i - 1;
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    auto ch = (word < vec.nwords)
                  ? static_cast<char>((vec.words[word].aval >> bit) & 0xFF)
                  : '\0';
    if (ch != 0) result += ch;
  }
  return result;
}

static Logic4Vec EvalStringCompare(TokenKind op, const Logic4Vec& lhs,
                                   const Logic4Vec& rhs, Arena& arena) {
  auto ls = PackedToStr(lhs);
  auto rs = PackedToStr(rhs);
  bool r = false;
  switch (op) {
    case TokenKind::kEqEq:
      r = (ls == rs);
      break;
    case TokenKind::kBangEq:
      r = (ls != rs);
      break;
    case TokenKind::kEqEqEq:
      r = (ls == rs);
      break;
    case TokenKind::kBangEqEq:
      r = (ls != rs);
      break;
    case TokenKind::kLt:
      r = (ls < rs);
      break;
    case TokenKind::kGt:
      r = (ls > rs);
      break;
    case TokenKind::kLtEq:
      r = (ls <= rs);
      break;
    case TokenKind::kGtEq:
      r = (ls >= rs);
      break;
    default:
      break;
  }
  return MakeLogic4VecVal(arena, 1, r ? 1 : 0);
}

static Logic4Vec EvalEqualityCompare(TokenKind op, Logic4Vec lhs, Logic4Vec rhs,
                                     Arena& arena) {
  if ((lhs.is_real || rhs.is_real) &&
      (op == TokenKind::kEqEq || op == TokenKind::kBangEq)) {
    double ld = RealValueOf(lhs);
    double rd = RealValueOf(rhs);
    bool eq = (ld == rd);
    return MakeLogic4VecVal(arena, 1, (op == TokenKind::kEqEq) == eq ? 1 : 0);
  }
  if (lhs.width != rhs.width) {
    bool sign_ext = lhs.is_signed && rhs.is_signed;
    uint32_t w = std::max(lhs.width, rhs.width);
    if (lhs.width < w) lhs = ExtendVec(lhs, w, sign_ext, arena);
    if (rhs.width < w) rhs = ExtendVec(rhs, w, sign_ext, arena);
  }
  uint64_t val = EvalEqualityOp(op, lhs, rhs);
  if (val == kResultX) return MakeAllX(arena, 1);
  return MakeLogic4VecVal(arena, 1, val);
}

static Logic4Vec EvalBinaryCompare(TokenKind op, Logic4Vec lhs, Logic4Vec rhs,
                                   Arena& arena) {
  if (op == TokenKind::kLtLt || op == TokenKind::kLtLtLt ||
      op == TokenKind::kGtGt || op == TokenKind::kGtGtGt) {
    if (HasUnknownBits(rhs)) return MakeAllX(arena, lhs.width);
    return EvalShift(op, lhs, ShiftCount(rhs), arena);
  }

  if (lhs.is_string || rhs.is_string) {
    return EvalStringCompare(op, lhs, rhs, arena);
  }
  if (IsEqualityOp(op)) {
    return EvalEqualityCompare(op, lhs, rhs, arena);
  }
  return EvalRelational(op, lhs, rhs, arena);
}
Logic4Vec EvalBinaryOp(TokenKind op, Logic4Vec lhs, Logic4Vec rhs, Arena& arena,
                       uint32_t context_width) {
  switch (op) {
    case TokenKind::kPlus:
    case TokenKind::kMinus:
    case TokenKind::kStar:
    case TokenKind::kSlash:
    case TokenKind::kPercent:
    case TokenKind::kPower:
      return EvalBinaryArith(op, lhs, rhs, arena, context_width);
    case TokenKind::kAmp:
    case TokenKind::kPipe:
    case TokenKind::kCaret:
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
      return EvalBinaryBitwise(op, lhs, rhs, arena, context_width);
    default:
      return EvalBinaryCompare(op, lhs, rhs, arena);
  }
}

}  // namespace delta
