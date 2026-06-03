#include "simulator/evaluation.h"

#include <algorithm>
#include <cmath>
#include <cstring>
#include <string>
#include <vector>

#include "common/arena.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"

namespace delta {
static Logic4Vec EvalIdentifier(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  auto* var = ctx.FindVariable(expr->text);
  if (var) {

    if (var->is_event)
      return MakeLogic4VecVal(arena, 1, var->is_null_event ? 0u : 1u);
    auto val = var->value;
    if (ctx.IsRealVariable(expr->text)) val.is_real = true;
    if (ctx.IsStringVariable(expr->text)) val.is_string = true;
    // An object's signedness is fixed by its own declaration; it is never
    // inherited from a value that flowed in from elsewhere (e.g. across a
    // module port). Derive the read value's signedness from the declaration
    // so a signed value stored into an unsigned object reads back unsigned.
    val.is_signed = var->is_signed;
    return val;
  }
  return MakeLogic4Vec(arena, 1);
}
bool HasUnknownBits(const Logic4Vec& v) {
  for (uint32_t i = 0; i < v.nwords; ++i) {
    if (v.words[i].bval != 0) return true;
  }
  return false;
}
Logic4Vec MakeAllX(Arena& arena, uint32_t width) {
  auto vec = MakeLogic4Vec(arena, width);
  for (uint32_t i = 0; i < vec.nwords; ++i) {
    vec.words[i] = {~uint64_t{0}, ~uint64_t{0}};
  }
  return vec;
}

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
static Logic4Vec EvalUnaryOp(TokenKind op, Logic4Vec operand, Arena& arena) {
  if (operand.nwords == 0) return operand;
  if (IsReductionOp(op)) return EvalReductionOp(op, operand, arena);
  auto result = MakeLogic4Vec(arena, operand.width);
  switch (op) {
    case TokenKind::kTilde: {
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
    case TokenKind::kBang:

      if (HasUnknownBits(operand)) return MakeAllX(arena, 1);
      return MakeLogic4VecVal(arena, 1, operand.ToUint64() == 0 ? 1 : 0);
    case TokenKind::kMinus: {
      if (operand.is_real) {
        double d = 0.0;
        uint64_t bits = operand.ToUint64();
        std::memcpy(&d, &bits, sizeof(double));
        d = -d;
        std::memcpy(&bits, &d, sizeof(double));
        auto r = MakeLogic4VecVal(arena, operand.width, bits);
        r.is_real = true;
        return r;
      }
      if (HasUnknownBits(operand)) return MakeAllX(arena, operand.width);
      uint64_t val = operand.ToUint64();
      auto r = MakeLogic4VecVal(arena, operand.width, -val);
      r.is_signed = operand.is_signed;
      return r;
    }
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

static Logic4Vec EvalSignedPow(int64_t base, int64_t exp, uint32_t width,
                               Arena& arena) {
  if (exp < 0) {
    if (base == 0) return MakeAllX(arena, width);
    int64_t r = 0;
    if (base == 1)
      r = 1;
    else if (base == -1)
      r = (exp % 2 == 0) ? 1 : -1;
    auto result = MakeLogic4VecVal(arena, width, static_cast<uint64_t>(r));
    result.is_signed = true;
    return result;
  }
  auto r = static_cast<int64_t>(IntPow(base, exp));
  auto result = MakeLogic4VecVal(arena, width, static_cast<uint64_t>(r));
  result.is_signed = true;
  return result;
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
      r = lv / rv;
      break;
    case TokenKind::kPercent:
      if (rv == 0) return MakeAllX(arena, width);
      r = lv % rv;
      break;
    case TokenKind::kPower:
      return EvalSignedPow(lv, rv, width, arena);
    default:
      break;
  }
  auto result = MakeLogic4VecVal(arena, width, static_cast<uint64_t>(r));
  result.is_signed = true;
  return result;
}

static double ToDouble(const Logic4Vec& v) {
  if (v.is_real) {
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
  return static_cast<double>(v.ToUint64());
}

static Logic4Vec MakeRealResult(Arena& arena, double val,
                                uint32_t result_width = 64) {
  if (result_width == 32) {
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
  double lv = ToDouble(lhs);
  double rv = ToDouble(rhs);
  uint32_t w = RealResultWidth(lhs, rhs);
  switch (op) {
    case TokenKind::kPlus:
      return MakeRealResult(arena, lv + rv, w);
    case TokenKind::kMinus:
      return MakeRealResult(arena, lv - rv, w);
    case TokenKind::kStar:
      return MakeRealResult(arena, lv * rv, w);
    case TokenKind::kSlash:
      if (rv == 0.0) return MakeAllX(arena, w);
      return MakeRealResult(arena, lv / rv, w);
    case TokenKind::kPower:
      return MakeRealResult(arena, std::pow(lv, rv), w);
    default:
      return MakeRealResult(arena, 0.0, w);
  }
}
static Logic4Vec EvalBinaryArith(TokenKind op, Logic4Vec lhs, Logic4Vec rhs,
                                 Arena& arena, uint32_t context_width = 0) {

  if (lhs.is_real || rhs.is_real) return EvalRealArith(op, lhs, rhs, arena);
  uint32_t self_w = (op == TokenKind::kPower)
                        ? lhs.width
                        : ((lhs.width > rhs.width) ? lhs.width : rhs.width);
  uint32_t width = (context_width > self_w) ? context_width : self_w;
  if (HasUnknownBits(lhs) || HasUnknownBits(rhs)) {
    return MakeAllX(arena, width);
  }

  if (lhs.is_signed && rhs.is_signed) {
    return EvalSignedArith(op, lhs, rhs, width, arena);
  }
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
    case TokenKind::kPower:
      result = IntPow(lv, rv);
      break;
    default:
      break;
  }
  return MakeLogic4VecVal(arena, width, result);
}
static Logic4Vec ExtendVec(const Logic4Vec& v, uint32_t target_width,
                           bool sign_ext, Arena& arena);
static Logic4Vec EvalBinaryBitwise(TokenKind op, Logic4Vec lhs, Logic4Vec rhs,
                                   Arena& arena, uint32_t context_width = 0) {
  uint32_t self_w = (lhs.width > rhs.width) ? lhs.width : rhs.width;
  uint32_t width = (context_width > self_w) ? context_width : self_w;

  if (lhs.width != rhs.width) {
    bool sign_ext = lhs.is_signed && rhs.is_signed;
    if (lhs.width < width) lhs = ExtendVec(lhs, width, sign_ext, arena);
    if (rhs.width < width) rhs = ExtendVec(rhs, width, sign_ext, arena);
  }
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
static Logic4Vec ExtendVec(const Logic4Vec& v, uint32_t target_width,
                           bool sign_ext, Arena& arena) {
  auto result = MakeLogic4Vec(arena, target_width);
  for (uint32_t i = 0; i < v.nwords; ++i) {
    result.words[i] = v.words[i];
  }
  if (sign_ext && v.width > 0) {
    uint32_t msb_idx = (v.width - 1) / 64;
    uint64_t msb_mask = uint64_t{1} << ((v.width - 1) % 64);
    uint64_t a_fill = (v.words[msb_idx].aval & msb_mask) ? ~uint64_t{0} : 0;
    uint64_t b_fill = (v.words[msb_idx].bval & msb_mask) ? ~uint64_t{0} : 0;
    if (a_fill || b_fill) {
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
  }
  result.is_signed = v.is_signed;
  result.is_real = v.is_real;
  result.is_string = v.is_string;
  return result;
}
static bool EvalCaseEquality(Logic4Vec lhs, Logic4Vec rhs) {
  if (lhs.width != rhs.width) return false;
  for (uint32_t i = 0; i < lhs.nwords; ++i) {
    if (lhs.words[i].aval != rhs.words[i].aval) return false;
    if (lhs.words[i].bval != rhs.words[i].bval) return false;
  }
  return true;
}
static Logic4Vec MakeSignedResult(Arena& arena, uint32_t width, uint64_t val,
                                  bool is_signed) {
  auto result = MakeLogic4VecVal(arena, width, val);
  result.is_signed = is_signed;
  return result;
}
static Logic4Vec EvalArithShiftRight(Logic4Vec lhs, uint64_t rv, Arena& arena) {
  uint64_t lv = lhs.ToUint64();
  uint64_t bv = lhs.nwords > 0 ? lhs.words[0].bval : 0;
  uint32_t w = lhs.width;
  auto shift_right = [&](uint64_t val) -> uint64_t {
    if (lhs.is_signed && w > 0 && w < 64 && ((val >> (w - 1)) & 1)) {
      auto sv = static_cast<int64_t>(val | (~uint64_t{0} << w));
      auto shifted = static_cast<uint64_t>(sv >> rv);
      return shifted & ((uint64_t{1} << w) - 1);
    }
    return val >> rv;
  };
  auto result = MakeSignedResult(arena, w, shift_right(lv), lhs.is_signed);
  if (result.nwords > 0) result.words[0].bval = shift_right(bv);
  return result;
}
static Logic4Vec EvalShift(TokenKind op, Logic4Vec lhs, uint64_t rv,
                           Arena& arena) {
  uint64_t lv = lhs.ToUint64();
  uint64_t bv = lhs.nwords > 0 ? lhs.words[0].bval : 0;
  if (op == TokenKind::kLtLt || op == TokenKind::kLtLtLt) {
    auto result = MakeSignedResult(arena, lhs.width, lv << rv, lhs.is_signed);
    if (result.nwords > 0) result.words[0].bval = bv << rv;
    return result;
  }
  if (op == TokenKind::kGtGt) {
    auto result = MakeSignedResult(arena, lhs.width, lv >> rv, lhs.is_signed);
    if (result.nwords > 0) result.words[0].bval = bv >> rv;
    return result;
  }
  return EvalArithShiftRight(lhs, rv, arena);
}

static constexpr uint64_t kResultX = 2;
static uint64_t EvalWildcardEq(Logic4Vec lhs, Logic4Vec rhs) {
  uint64_t rhs_dc = rhs.nwords > 0 ? rhs.words[0].bval : 0;
  uint64_t lhs_x = lhs.nwords > 0 ? lhs.words[0].bval : 0;

  if (lhs_x & ~rhs_dc) return kResultX;
  return (((lhs.ToUint64() ^ rhs.ToUint64()) & ~rhs_dc) == 0) ? 1 : 0;
}
static uint64_t EvalEqualityOp(TokenKind op, Logic4Vec lhs, Logic4Vec rhs) {
  switch (op) {
    case TokenKind::kEqEq:
    case TokenKind::kBangEq:

      if (HasUnknownBits(lhs) || HasUnknownBits(rhs)) return kResultX;
      return (op == TokenKind::kEqEq) == (lhs.ToUint64() == rhs.ToUint64()) ? 1
                                                                            : 0;
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
int64_t SignExtend(uint64_t val, uint32_t width) {
  if (width == 0 || width >= 64) return static_cast<int64_t>(val);
  uint64_t mask = uint64_t{1} << (width - 1);
  return static_cast<int64_t>((val ^ mask) - mask);
}

int64_t AssocIntKey(const Logic4Vec& val, bool is_wildcard,
                    uint32_t index_width, bool is_signed) {
  // A wildcard index keeps its self-determined, unsigned value. A typed
  // integral index is cast to its declared width per §7.8.4: a signed index
  // type is sign-extended, an unsigned index type is zero-extended. Because
  // the key map orders by signed int64, a zero-extended (non-negative) key
  // yields the unsigned numeric ordering an unsigned index type requires.
  if (is_wildcard) return static_cast<int64_t>(val.ToUint64());
  if (is_signed) return SignExtend(val.ToUint64(), index_width);
  uint64_t raw = val.ToUint64();
  if (index_width < 64) raw &= (uint64_t{1} << index_width) - 1;
  return static_cast<int64_t>(raw);
}

static uint64_t EvalRelationalOp(TokenKind op, uint64_t lv, uint64_t rv) {
  switch (op) {
    case TokenKind::kLt:
      return (lv < rv) ? 1 : 0;
    case TokenKind::kGt:
      return (lv > rv) ? 1 : 0;
    case TokenKind::kLtEq:
      return (lv <= rv) ? 1 : 0;
    case TokenKind::kGtEq:
      return (lv >= rv) ? 1 : 0;
    default:
      return 0;
  }
}
static uint64_t EvalSignedRelOp(TokenKind op, int64_t lv, int64_t rv) {
  switch (op) {
    case TokenKind::kLt:
      return (lv < rv) ? 1 : 0;
    case TokenKind::kGt:
      return (lv > rv) ? 1 : 0;
    case TokenKind::kLtEq:
      return (lv <= rv) ? 1 : 0;
    case TokenKind::kGtEq:
      return (lv >= rv) ? 1 : 0;
    default:
      return 0;
  }
}
static bool IsEqualityOp(TokenKind op) {
  return op == TokenKind::kEqEq || op == TokenKind::kEqEqEq ||
         op == TokenKind::kBangEq || op == TokenKind::kBangEqEq ||
         op == TokenKind::kEqEqQuestion || op == TokenKind::kBangEqQuestion;
}

static Logic4Vec EvalRealRelational(TokenKind op, const Logic4Vec& lhs,
                                    const Logic4Vec& rhs, Arena& arena) {
  double ld = ToDouble(lhs);
  double rd = ToDouble(rhs);
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
  if (lhs.is_signed && rhs.is_signed) {
    int64_t lv = SignExtend(lhs.ToUint64(), lhs.width);
    int64_t rv = SignExtend(rhs.ToUint64(), rhs.width);
    return MakeLogic4VecVal(arena, 1, EvalSignedRelOp(op, lv, rv));
  }
  return MakeLogic4VecVal(arena, 1,
                          EvalRelationalOp(op, lhs.ToUint64(), rhs.ToUint64()));
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

static Logic4Vec EvalBinaryCompare(TokenKind op, Logic4Vec lhs, Logic4Vec rhs,
                                   Arena& arena) {
  if (op == TokenKind::kLtLt || op == TokenKind::kLtLtLt ||
      op == TokenKind::kGtGt || op == TokenKind::kGtGtGt) {
    if (HasUnknownBits(rhs)) return MakeAllX(arena, lhs.width);
    return EvalShift(op, lhs, rhs.ToUint64(), arena);
  }

  if (lhs.is_string || rhs.is_string) {
    return EvalStringCompare(op, lhs, rhs, arena);
  }
  if (IsEqualityOp(op)) {
    if ((lhs.is_real || rhs.is_real) &&
        (op == TokenKind::kEqEq || op == TokenKind::kBangEq)) {
      double ld = ToDouble(lhs);
      double rd = ToDouble(rhs);
      bool eq = (ld == rd);
      return MakeLogic4VecVal(arena, 1,
                              (op == TokenKind::kEqEq) == eq ? 1 : 0);
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
Logic4Vec AssembleConcatParts(const std::vector<Logic4Vec>& parts,
                              uint32_t total_width, Arena& arena) {
  auto result = MakeLogic4Vec(arena, total_width);
  uint32_t bit_pos = 0;
  for (auto it = parts.rbegin(); it != parts.rend(); ++it) {
    uint64_t aval = it->ToUint64();
    uint64_t bval = (it->nwords > 0) ? it->words[0].bval : 0;
    uint32_t w = it->width;
    if (w > 64) w = 64;
    uint32_t word = bit_pos / 64;
    uint32_t bit = bit_pos % 64;
    if (word < result.nwords) {
      result.words[word].aval |= aval << bit;
      result.words[word].bval |= bval << bit;
      if (bit + w > 64 && word + 1 < result.nwords) {
        result.words[word + 1].aval |= aval >> (64 - bit);
        result.words[word + 1].bval |= bval >> (64 - bit);
      }
    }
    bit_pos += it->width;
  }
  return result;
}

static Logic4Vec SelfDeterminedOperand(const Expr* elem, Logic4Vec vec,
                                       Arena& arena) {
  // Concatenation operands are self-determined; an unbased unsized
  // literal contributes one bit (per §5.7.1) rather than its default
  // wide carrier.
  if (elem && elem->kind == ExprKind::kUnbasedUnsizedLiteral &&
      vec.width > 1) {
    auto bit = MakeLogic4Vec(arena, 1);
    if (vec.nwords > 0) {
      bit.words[0].aval = vec.words[0].aval & 1;
      bit.words[0].bval = vec.words[0].bval & 1;
    }
    return bit;
  }
  return vec;
}

static Logic4Vec EvalConcat(const Expr* expr, SimContext& ctx, Arena& arena) {
  uint32_t total_width = 0;
  bool any_string = false;
  std::vector<Logic4Vec> parts;
  for (auto* elem : expr->elements) {
    auto vec = EvalExpr(elem, ctx, arena);
    vec = SelfDeterminedOperand(elem, vec, arena);
    parts.push_back(vec);
    if (parts.back().is_string) any_string = true;
    total_width += parts.back().width;
  }
  if (total_width == 0) return MakeLogic4Vec(arena, 1);
  auto result = AssembleConcatParts(parts, total_width, arena);
  result.is_string = any_string;
  return result;
}

static Logic4Vec CombineBranches(Logic4Vec tv, Logic4Vec fv, Arena& arena) {
  uint32_t width = (tv.width > fv.width) ? tv.width : fv.width;
  auto result = MakeLogic4Vec(arena, width);
  for (uint32_t i = 0; i < result.nwords; ++i) {
    auto tw = (i < tv.nwords) ? tv.words[i] : Logic4Word{};
    auto fw = (i < fv.nwords) ? fv.words[i] : Logic4Word{};
    result.words[i].aval = tw.aval & fw.aval;
    result.words[i].bval = tw.bval | fw.bval | (tw.aval ^ fw.aval);
  }
  if (tv.is_real || fv.is_real) result.is_real = true;
  return result;
}
static Logic4Vec EvalTernary(const Expr* expr, SimContext& ctx, Arena& arena,
                             uint32_t context_width = 0) {
  auto cond = EvalExpr(expr->condition, ctx, arena);

  if (HasUnknownBits(cond)) {
    auto tv = EvalExpr(expr->true_expr, ctx, arena, context_width);
    auto fv = EvalExpr(expr->false_expr, ctx, arena, context_width);
    bool result_signed = tv.is_signed && fv.is_signed;
    uint32_t width = (tv.width > fv.width) ? tv.width : fv.width;
    if (context_width > width) width = context_width;
    if (tv.width < width)
      tv = ExtendVec(tv, width, result_signed, arena);
    if (fv.width < width)
      fv = ExtendVec(fv, width, result_signed, arena);
    if (EvalCaseEquality(tv, fv)) {
      tv.is_signed = result_signed;
      return tv;
    }
    auto result = CombineBranches(tv, fv, arena);
    result.is_signed = result_signed;
    return result;
  }
  auto tv = EvalExpr(expr->true_expr, ctx, arena, context_width);
  auto fv = EvalExpr(expr->false_expr, ctx, arena, context_width);
  bool result_signed = tv.is_signed && fv.is_signed;
  uint32_t width = (tv.width > fv.width) ? tv.width : fv.width;
  if (context_width > width) width = context_width;
  auto& chosen = (cond.ToUint64() != 0) ? tv : fv;
  if (chosen.width < width) {
    auto extended = ExtendVec(chosen, width, result_signed, arena);
    extended.is_signed = result_signed;
    return extended;
  }
  chosen.is_signed = result_signed;
  return chosen;
}

static uint32_t AssignExprLhsWidth(const Expr* lhs, SimContext& ctx) {
  if (lhs->kind == ExprKind::kConcatenation) {
    uint32_t total = 0;
    for (auto* elem : lhs->elements) total += AssignExprLhsWidth(elem, ctx);
    return total;
  }
  auto* var = ResolveLhsVariable(lhs, ctx);
  return var ? var->value.width : 0;
}

static Logic4Vec EvalAssignInExpr(const Expr* expr, SimContext& ctx,
                                  Arena& arena) {
  auto rhs_val = EvalExpr(expr->rhs, ctx, arena);
  uint32_t lhs_w = AssignExprLhsWidth(expr->lhs, ctx);
  if (lhs_w == 0) return rhs_val;
  PerformBlockingAssign(expr->lhs, rhs_val, ctx, arena);
  // §11.3.6: a concatenation target yields an unsigned integral result whose
  // width is the sum of its operand widths. Re-pack the value rather than
  // forwarding the right-hand side so the result never inherits the
  // right-hand side's signedness, even when the widths already match.
  bool lhs_is_concat = expr->lhs->kind == ExprKind::kConcatenation;
  if (lhs_w == rhs_val.width && !lhs_is_concat) return rhs_val;
  uint64_t v = rhs_val.ToUint64();
  if (lhs_w < 64) v &= (uint64_t{1} << lhs_w) - 1;
  return MakeLogic4VecVal(arena, lhs_w, v);
}

static bool ArrayElementsEqual(std::string_view a, const ArrayInfo* ai,
                               std::string_view b, SimContext& ctx) {
  for (uint32_t i = 0; i < ai->size; ++i) {
    auto an = std::string(a) + "[" + std::to_string(ai->lo + i) + "]";
    auto bn = std::string(b) + "[" + std::to_string(ai->lo + i) + "]";
    auto* av = ctx.FindVariable(an);
    auto* bv = ctx.FindVariable(bn);
    if (!av || !bv) return false;
    if (av->value.ToUint64() != bv->value.ToUint64()) return false;
  }
  return true;
}

static bool TryArrayEqualityOp(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out) {
  if (expr->op != TokenKind::kEqEq && expr->op != TokenKind::kBangEq)
    return false;
  if (!expr->lhs || !expr->rhs) return false;
  if (expr->lhs->kind != ExprKind::kIdentifier) return false;
  if (expr->rhs->kind != ExprKind::kIdentifier) return false;
  auto* la = ctx.FindArrayInfo(expr->lhs->text);
  auto* ra = ctx.FindArrayInfo(expr->rhs->text);
  if (!la || !ra) return false;
  bool eq = (la->size == ra->size && la->elem_width == ra->elem_width);
  if (eq) eq = ArrayElementsEqual(expr->lhs->text, la, expr->rhs->text, ctx);
  uint64_t val = (expr->op == TokenKind::kEqEq) == eq ? 1 : 0;
  out = MakeLogic4VecVal(arena, 1, val);
  return true;
}

static Logic4Vec EvalLogicalAnd(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  auto l = EvalExpr(expr->lhs, ctx, arena);
  bool l_unknown = HasUnknownBits(l);
  if (!l_unknown && l.ToUint64() == 0) {
    return MakeLogic4VecVal(arena, 1, 0);
  }
  auto r = EvalExpr(expr->rhs, ctx, arena);
  bool r_unknown = HasUnknownBits(r);
  if (!r_unknown && r.ToUint64() == 0) {
    return MakeLogic4VecVal(arena, 1, 0);
  }
  if (l_unknown || r_unknown) return MakeAllX(arena, 1);
  return MakeLogic4VecVal(arena, 1, 1);
}

static Logic4Vec EvalLogicalOr(const Expr* expr, SimContext& ctx,
                               Arena& arena) {
  auto l = EvalExpr(expr->lhs, ctx, arena);
  bool l_unknown = HasUnknownBits(l);
  if (!l_unknown && l.ToUint64() != 0) {
    return MakeLogic4VecVal(arena, 1, 1);
  }
  auto r = EvalExpr(expr->rhs, ctx, arena);
  bool r_unknown = HasUnknownBits(r);
  if (!r_unknown && r.ToUint64() != 0) {
    return MakeLogic4VecVal(arena, 1, 1);
  }
  if (l_unknown || r_unknown) return MakeAllX(arena, 1);
  return MakeLogic4VecVal(arena, 1, 0);
}

static Logic4Vec EvalLogicalImpl(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  auto l = EvalExpr(expr->lhs, ctx, arena);
  bool l_unknown = HasUnknownBits(l);
  if (!l_unknown && l.ToUint64() == 0) {
    return MakeLogic4VecVal(arena, 1, 1);
  }
  auto r = EvalExpr(expr->rhs, ctx, arena);
  bool r_unknown = HasUnknownBits(r);
  if (!r_unknown && r.ToUint64() != 0) {
    return MakeLogic4VecVal(arena, 1, 1);
  }
  if (l_unknown || r_unknown) return MakeAllX(arena, 1);
  return MakeLogic4VecVal(arena, 1, 0);
}

static Logic4Vec EvalLogicalEquiv(const Expr* expr, SimContext& ctx,
                                  Arena& arena) {
  auto l = EvalExpr(expr->lhs, ctx, arena);
  auto r = EvalExpr(expr->rhs, ctx, arena);
  bool l_unknown = HasUnknownBits(l);
  bool r_unknown = HasUnknownBits(r);
  if (l_unknown || r_unknown) return MakeAllX(arena, 1);
  bool lv = l.ToUint64() != 0;
  bool rv = r.ToUint64() != 0;
  return MakeLogic4VecVal(arena, 1, (lv == rv) ? 1 : 0);
}
static Logic4Vec EvalBinaryExpr(const Expr* expr, SimContext& ctx, Arena& arena,
                                uint32_t context_width = 0) {
  if (expr->op == TokenKind::kEq) return EvalAssignInExpr(expr, ctx, arena);
  {
    Logic4Vec arr_result;
    if (TryArrayEqualityOp(expr, ctx, arena, arr_result)) return arr_result;
  }
  if (expr->op == TokenKind::kAmpAmp) return EvalLogicalAnd(expr, ctx, arena);

  if (expr->op == TokenKind::kAmpAmpAmp) {
    auto lv = EvalExpr(expr->lhs, ctx, arena);
    if (!lv.IsTruthy()) return MakeLogic4VecVal(arena, 1, 0);
    auto rv = EvalExpr(expr->rhs, ctx, arena);
    return MakeLogic4VecVal(arena, 1, rv.IsTruthy() ? 1 : 0);
  }
  if (expr->op == TokenKind::kPipePipe) return EvalLogicalOr(expr, ctx, arena);
  if (expr->op == TokenKind::kArrow) return EvalLogicalImpl(expr, ctx, arena);
  if (expr->op == TokenKind::kLtDashGt)
    return EvalLogicalEquiv(expr, ctx, arena);

  if (expr->op == TokenKind::kEqEq || expr->op == TokenKind::kBangEq ||
      expr->op == TokenKind::kEqEqEq || expr->op == TokenKind::kBangEqEq) {
    auto* lhs_id = (expr->lhs && expr->lhs->kind == ExprKind::kIdentifier)
                        ? expr->lhs
                        : nullptr;
    auto* rhs_id = (expr->rhs && expr->rhs->kind == ExprKind::kIdentifier)
                        ? expr->rhs
                        : nullptr;
    Variable* lv = lhs_id ? ctx.FindVariable(lhs_id->text) : nullptr;
    Variable* rv = rhs_id ? ctx.FindVariable(rhs_id->text) : nullptr;
    bool lhs_is_event = lv && lv->is_event;
    bool rhs_is_event = rv && rv->is_event;
    bool lhs_is_null =
        lhs_id && lhs_id->text == "null" && !lv;
    bool rhs_is_null =
        rhs_id && rhs_id->text == "null" && !rv;
    if (lhs_is_event || rhs_is_event) {
      bool equal = false;
      if (lhs_is_event && rhs_is_event) {
        equal = (lv == rv);
      } else if (lhs_is_event && rhs_is_null) {
        equal = lv->is_null_event;
      } else if (rhs_is_event && lhs_is_null) {
        equal = rv->is_null_event;
      }
      bool is_eq_op = (expr->op == TokenKind::kEqEq ||
                        expr->op == TokenKind::kEqEqEq);
      return MakeLogic4VecVal(arena, 1,
                              (is_eq_op == equal) ? 1u : 0u);
    }

    // §25.9: equality of a virtual interface against another virtual interface,
    // an interface instance, or null compares the interface instance each side
    // refers to (an unbound virtual interface and null compare equal).
    bool lhs_is_vi = ctx.IsVirtualInterfaceVar(lv);
    bool rhs_is_vi = ctx.IsVirtualInterfaceVar(rv);
    if (lhs_is_vi || rhs_is_vi) {
      auto operand_scope = [&](Variable* v, const Expr* id, bool is_vi,
                               bool is_null) -> std::string {
        if (is_vi) return std::string(ctx.VirtualInterfaceBinding(v));
        if (is_null) return std::string();
        if (id) return ctx.ResolveInstanceScope(id->text);
        return std::string();
      };
      std::string ls = operand_scope(lv, lhs_id, lhs_is_vi, lhs_is_null);
      std::string rs = operand_scope(rv, rhs_id, rhs_is_vi, rhs_is_null);
      bool equal = (ls == rs);
      bool is_eq_op = (expr->op == TokenKind::kEqEq ||
                       expr->op == TokenKind::kEqEqEq);
      return MakeLogic4VecVal(arena, 1, (is_eq_op == equal) ? 1u : 0u);
    }
  }
  return EvalBinaryOp(expr->op, EvalExpr(expr->lhs, ctx, arena),
                      EvalExpr(expr->rhs, ctx, arena), arena, context_width);
}

static Logic4Vec EvalTaggedExpr(const Expr* expr, SimContext& ctx,
                                Arena& arena, uint32_t context_width = 0) {

  if (expr->lhs) return EvalExpr(expr->lhs, ctx, arena, context_width);

  return MakeLogic4VecVal(arena, 1, 0);
}

Logic4Vec EvalExpr(const Expr* expr, SimContext& ctx, Arena& arena,
                   uint32_t context_width) {
  if (!expr) return MakeLogic4Vec(arena, 1);

  if (const auto* snap = ctx.FindDeferredArgSnapshot(expr)) {
    return *snap;
  }
  switch (expr->kind) {
    case ExprKind::kIntegerLiteral:
      return EvalIntLiteral(expr, arena);
    case ExprKind::kUnbasedUnsizedLiteral:
      return EvalUnbasedUnsized(expr, arena);
    case ExprKind::kStringLiteral:
      return EvalStringLiteral(expr, arena);
    case ExprKind::kRealLiteral:
    case ExprKind::kTimeLiteral: {
      double v = expr->real_val;
      uint64_t bits = 0;
      std::memcpy(&bits, &v, sizeof(double));
      auto rv = MakeLogic4VecVal(arena, 64, bits);
      rv.is_real = true;
      return rv;
    }
    case ExprKind::kIdentifier:
      return EvalIdentifier(expr, ctx, arena);
    case ExprKind::kUnary:
      if (expr->op == TokenKind::kPlusPlus ||
          expr->op == TokenKind::kMinusMinus) {
        return EvalPrefixUnary(expr, ctx, arena);
      }
      return EvalUnaryOp(expr->op, EvalExpr(expr->lhs, ctx, arena), arena);
    case ExprKind::kBinary:
      if (IsCompoundAssignOp(expr->op)) {
        return EvalCompoundAssign(expr, ctx, arena);
      }
      if (expr->op == TokenKind::kKwMatches) {
        return EvalMatches(expr, ctx, arena);
      }
      return EvalBinaryExpr(expr, ctx, arena, context_width);
    case ExprKind::kTernary:
      return EvalTernary(expr, ctx, arena, context_width);
    case ExprKind::kConcatenation:
      return EvalConcat(expr, ctx, arena);
    case ExprKind::kReplicate:
      return EvalReplicate(expr, ctx, arena);
    case ExprKind::kSelect:
      return EvalSelect(expr, ctx, arena);
    case ExprKind::kSystemCall:
      return EvalSystemCall(expr, ctx, arena);
    case ExprKind::kCall:
      return EvalFunctionCall(expr, ctx, arena);
    case ExprKind::kPostfixUnary:
      return EvalPostfixUnary(expr, ctx, arena);
    case ExprKind::kMemberAccess:
      return EvalMemberAccess(expr, ctx, arena);
    case ExprKind::kCast:
      return EvalCast(expr, ctx, arena);
    case ExprKind::kInside:
      return EvalInside(expr, ctx, arena);
    case ExprKind::kStreamingConcat:
      return EvalStreamingConcat(expr, ctx, arena);
    case ExprKind::kAssignmentPattern:
      return EvalAssignmentPattern(expr, ctx, arena);
    case ExprKind::kTagged:
      return EvalTaggedExpr(expr, ctx, arena, context_width);
    case ExprKind::kMinTypMax: {
      DelayMode mode = ctx.GetDelayMode();
      if (mode == DelayMode::kMin)
        return EvalExpr(expr->lhs, ctx, arena, context_width);
      if (mode == DelayMode::kMax)
        return EvalExpr(expr->rhs, ctx, arena, context_width);
      return EvalExpr(expr->condition, ctx, arena, context_width);
    }
    default:
      return MakeLogic4Vec(arena, 1);
  }
}

}
