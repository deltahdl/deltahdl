#include "simulation/eval.h"

#include <cstring>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaboration/type_eval.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulation/sim_context.h"

namespace delta {

// --- Literal evaluation ---

static uint32_t LiteralWidth(std::string_view text, uint64_t val) {
  auto tick = text.find('\'');
  if (tick != std::string_view::npos && tick > 0) {
    uint32_t w = 0;
    for (size_t i = 0; i < tick; ++i) {
      if (text[i] >= '0' && text[i] <= '9') w = w * 10 + (text[i] - '0');
    }
    if (w > 0) return w;
  }
  return (val > UINT32_MAX) ? 64 : 32;
}

static Logic4Vec EvalUnbasedUnsized(const Expr* expr, Arena& arena) {
  // §5.7.1: '0, '1, 'x, 'z — single-bit unbased unsized literal.
  auto text = expr->text;
  if (text.size() >= 2 && text[0] == '\'') {
    char c = text[1];
    if (c == '1') return MakeLogic4VecVal(arena, 1, 1);
    if (c == '0') return MakeLogic4VecVal(arena, 1, 0);
    // 'x and 'z: set bval to indicate unknown.
    auto vec = MakeLogic4Vec(arena, 1);
    if (c == 'x' || c == 'X') vec.words[0] = {1, 1};
    if (c == 'z' || c == 'Z' || c == '?') vec.words[0] = {0, 1};
    return vec;
  }
  return MakeLogic4VecVal(arena, 1, expr->int_val);
}

// Check if a based literal's digit string contains x/z characters.
static bool TextHasXZ(std::string_view text) {
  auto tick = text.find('\'');
  if (tick == std::string_view::npos) return false;
  for (size_t i = tick + 1; i < text.size(); ++i) {
    char c = text[i];
    if (c == 'x' || c == 'X' || c == 'z' || c == 'Z' || c == '?') return true;
  }
  return false;
}

// Bits per digit for each base letter.
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

// Parse a digit's numeric value (0-15), or -1 for x/z.
static int DigitValue(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}

// Set bit_count bits starting at bit_pos in vec for an x/z/normal digit.
static void SetDigitBits(Logic4Vec& vec, uint32_t& bit_pos, int bit_count,
                         char digit, uint32_t width) {
  bool is_x = (digit == 'x' || digit == 'X');
  bool is_z = (digit == 'z' || digit == 'Z' || digit == '?');
  int dval = DigitValue(digit);
  for (int b = 0; b < bit_count && bit_pos < width; ++b, ++bit_pos) {
    uint32_t word = bit_pos / 64;
    uint64_t mask = uint64_t{1} << (bit_pos % 64);
    if (is_x) {
      vec.words[word].aval |= mask;
      vec.words[word].bval |= mask;
    } else if (is_z) {
      vec.words[word].bval |= mask;
    } else if (dval >= 0 && (dval & (1 << b))) {
      vec.words[word].aval |= mask;
    }
  }
}

// Parse a based literal with x/z digits into a Logic4Vec.
static Logic4Vec ParseBasedXZLiteral(std::string_view text, uint32_t width,
                                     Arena& arena) {
  auto vec = MakeLogic4Vec(arena, width);
  std::string buf;
  buf.reserve(text.size());
  for (char c : text)
    if (c != '_') buf.push_back(c);
  auto tick = buf.find('\'');
  if (tick == std::string::npos) return vec;
  size_t i = tick + 1;
  if (i < buf.size() && (buf[i] == 's' || buf[i] == 'S')) ++i;
  int bpd = (i < buf.size()) ? BitsPerDigit(buf[i]) : 0;
  if (bpd == 0) return vec;  // Decimal x/z: leave as zero.
  ++i;
  uint32_t bit_pos = 0;
  for (auto j = buf.size(); j > i && bit_pos < width; --j)
    SetDigitBits(vec, bit_pos, bpd, buf[j - 1], width);
  return vec;
}

static Logic4Vec EvalIntLiteral(const Expr* expr, Arena& arena) {
  uint32_t width = LiteralWidth(expr->text, expr->int_val);
  if (TextHasXZ(expr->text))
    return ParseBasedXZLiteral(expr->text, width, arena);
  return MakeLogic4VecVal(arena, width, expr->int_val);
}

static Logic4Vec EvalStringLiteral(const Expr* expr, Arena& arena) {
  auto text = expr->text;
  // Strip surrounding quotes.
  if (text.size() >= 2 && text.front() == '"') {
    text = text.substr(1, text.size() - 2);
  }
  uint32_t width = static_cast<uint32_t>(text.size()) * 8;
  if (width == 0) width = 8;
  auto vec = MakeLogic4Vec(arena, width);
  for (size_t i = 0; i < text.size(); ++i) {
    auto byte_idx = static_cast<uint32_t>(text.size() - 1 - i);
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    vec.words[word].aval |= static_cast<uint64_t>(text[i]) << bit;
  }
  return vec;
}

// --- Identifier evaluation ---

static Logic4Vec EvalIdentifier(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  auto* var = ctx.FindVariable(expr->text);
  if (var) {
    auto val = var->value;
    if (ctx.IsRealVariable(expr->text)) val.is_real = true;
    if (var->is_signed) val.is_signed = true;
    return val;
  }
  return MakeLogic4Vec(arena, 1);  // X for unknown
}

// --- Reduction operations (§11.4.9) ---

static uint64_t ReduceBits(uint64_t val, uint32_t width) {
  uint64_t mask = (width >= 64) ? ~uint64_t{0} : (uint64_t{1} << width) - 1;
  return val & mask;
}

static Logic4Vec EvalReductionOp(TokenKind op, Logic4Vec operand,
                                 Arena& arena) {
  uint64_t val = ReduceBits(operand.ToUint64(), operand.width);
  uint64_t all_ones =
      (operand.width >= 64) ? ~uint64_t{0} : (uint64_t{1} << operand.width) - 1;
  uint64_t bit_count = __builtin_popcountll(val);
  switch (op) {
    case TokenKind::kAmp:
      return MakeLogic4VecVal(arena, 1, (val == all_ones) ? 1 : 0);
    case TokenKind::kPipe:
      return MakeLogic4VecVal(arena, 1, (val != 0) ? 1 : 0);
    case TokenKind::kCaret:
      return MakeLogic4VecVal(arena, 1, bit_count & 1);
    case TokenKind::kTildeAmp:
      return MakeLogic4VecVal(arena, 1, (val == all_ones) ? 0 : 1);
    case TokenKind::kTildePipe:
      return MakeLogic4VecVal(arena, 1, (val != 0) ? 0 : 1);
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
      return MakeLogic4VecVal(arena, 1, (bit_count & 1) ? 0 : 1);
    default:
      return operand;
  }
}

// --- Unary operations ---

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
    case TokenKind::kTilde:
      for (uint32_t i = 0; i < result.nwords; ++i) {
        result.words[i] = Logic4Not(operand.words[i]);
      }
      return result;
    case TokenKind::kBang: {
      uint64_t val = operand.ToUint64();
      return MakeLogic4VecVal(arena, 1, val == 0 ? 1 : 0);
    }
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
      uint64_t val = operand.ToUint64();
      return MakeLogic4VecVal(arena, operand.width, -val);
    }
    default:
      return operand;
  }
}

// --- Binary arithmetic ---

static uint64_t IntPow(uint64_t base, uint64_t exp) {
  uint64_t result = 1;
  while (exp > 0) {
    if (exp & 1) result *= base;
    base *= base;
    exp >>= 1;
  }
  return result;
}

static Logic4Vec EvalBinaryArith(TokenKind op, Logic4Vec lhs, Logic4Vec rhs,
                                 Arena& arena) {
  uint64_t lv = lhs.ToUint64();
  uint64_t rv = rhs.ToUint64();
  uint32_t width = (lhs.width > rhs.width) ? lhs.width : rhs.width;
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
      result = (rv != 0) ? lv / rv : 0;
      break;
    case TokenKind::kPercent:
      result = (rv != 0) ? lv % rv : 0;
      break;
    case TokenKind::kPower:
      result = IntPow(lv, rv);
      break;
    default:
      break;
  }
  return MakeLogic4VecVal(arena, width, result);
}

// --- Binary bitwise ---

static Logic4Vec EvalBinaryBitwise(TokenKind op, Logic4Vec lhs, Logic4Vec rhs,
                                   Arena& arena) {
  uint32_t width = (lhs.width > rhs.width) ? lhs.width : rhs.width;
  auto result = MakeLogic4Vec(arena, width);
  uint32_t words = result.nwords;

  for (uint32_t i = 0; i < words; ++i) {
    auto lw = (i < lhs.nwords) ? lhs.words[i] : Logic4Word{};
    auto rw = (i < rhs.nwords) ? rhs.words[i] : Logic4Word{};
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
      default:
        break;
    }
  }
  return result;
}

// --- Case equality (compares both aval and bval) ---

static bool EvalCaseEquality(Logic4Vec lhs, Logic4Vec rhs) {
  if (lhs.width != rhs.width) return false;
  for (uint32_t i = 0; i < lhs.nwords; ++i) {
    if (lhs.words[i].aval != rhs.words[i].aval) return false;
    if (lhs.words[i].bval != rhs.words[i].bval) return false;
  }
  return true;
}

// --- Shift operations ---

static Logic4Vec MakeSignedResult(Arena& arena, uint32_t width, uint64_t val,
                                  bool is_signed) {
  auto result = MakeLogic4VecVal(arena, width, val);
  result.is_signed = is_signed;
  return result;
}

static Logic4Vec EvalArithShiftRight(Logic4Vec lhs, uint64_t rv, Arena& arena) {
  uint64_t lv = lhs.ToUint64();
  uint32_t w = lhs.width;
  if (w > 0 && w < 64 && ((lv >> (w - 1)) & 1)) {
    auto sv = static_cast<int64_t>(lv | (~uint64_t{0} << w));
    auto shifted = static_cast<uint64_t>(sv >> rv);
    uint64_t mask = (w >= 64) ? ~uint64_t{0} : (uint64_t{1} << w) - 1;
    return MakeSignedResult(arena, w, shifted & mask, lhs.is_signed);
  }
  return MakeSignedResult(arena, lhs.width, lv >> rv, lhs.is_signed);
}

static Logic4Vec EvalShift(TokenKind op, Logic4Vec lhs, uint64_t rv,
                           Arena& arena) {
  uint64_t lv = lhs.ToUint64();
  if (op == TokenKind::kLtLt || op == TokenKind::kLtLtLt) {
    return MakeSignedResult(arena, lhs.width, lv << rv, lhs.is_signed);
  }
  if (op == TokenKind::kGtGt) {
    return MakeSignedResult(arena, lhs.width, lv >> rv, lhs.is_signed);
  }
  return EvalArithShiftRight(lhs, rv, arena);
}

// --- Wildcard equality ---

static uint64_t EvalWildcardEq(Logic4Vec lhs, Logic4Vec rhs) {
  uint64_t rhs_dc = rhs.nwords > 0 ? rhs.words[0].bval : 0;
  return (((lhs.ToUint64() ^ rhs.ToUint64()) & ~rhs_dc) == 0) ? 1 : 0;
}

// --- Equality operations (§11.4.5, §11.4.6) ---

static uint64_t EvalEqualityOp(TokenKind op, Logic4Vec lhs, Logic4Vec rhs) {
  uint64_t lv = lhs.ToUint64();
  uint64_t rv = rhs.ToUint64();
  switch (op) {
    case TokenKind::kEqEq:
      return (lv == rv) ? 1 : 0;
    case TokenKind::kEqEqEq:
      return EvalCaseEquality(lhs, rhs) ? 1 : 0;
    case TokenKind::kBangEq:
      return (lv != rv) ? 1 : 0;
    case TokenKind::kBangEqEq:
      return EvalCaseEquality(lhs, rhs) ? 0 : 1;
    case TokenKind::kEqEqQuestion:
      return EvalWildcardEq(lhs, rhs);
    case TokenKind::kBangEqQuestion:
      return EvalWildcardEq(lhs, rhs) ^ 1;
    default:
      return 0;
  }
}

// --- Relational and logical operations (§11.4.4, §11.4.7) ---

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
    case TokenKind::kAmpAmp:
      return (lv != 0 && rv != 0) ? 1 : 0;
    case TokenKind::kPipePipe:
      return (lv != 0 || rv != 0) ? 1 : 0;
    default:
      return 0;
  }
}

// --- Binary comparison dispatch ---

static bool IsEqualityOp(TokenKind op) {
  return op == TokenKind::kEqEq || op == TokenKind::kEqEqEq ||
         op == TokenKind::kBangEq || op == TokenKind::kBangEqEq ||
         op == TokenKind::kEqEqQuestion || op == TokenKind::kBangEqQuestion;
}

static Logic4Vec EvalBinaryCompare(TokenKind op, Logic4Vec lhs, Logic4Vec rhs,
                                   Arena& arena) {
  if (op == TokenKind::kLtLt || op == TokenKind::kLtLtLt ||
      op == TokenKind::kGtGt || op == TokenKind::kGtGtGt) {
    return EvalShift(op, lhs, rhs.ToUint64(), arena);
  }
  if (IsEqualityOp(op)) {
    return MakeLogic4VecVal(arena, 1, EvalEqualityOp(op, lhs, rhs));
  }
  return MakeLogic4VecVal(arena, 1,
                          EvalRelationalOp(op, lhs.ToUint64(), rhs.ToUint64()));
}

// --- Binary dispatch ---

static Logic4Vec EvalBinaryOp(TokenKind op, Logic4Vec lhs, Logic4Vec rhs,
                              Arena& arena) {
  switch (op) {
    case TokenKind::kPlus:
    case TokenKind::kMinus:
    case TokenKind::kStar:
    case TokenKind::kSlash:
    case TokenKind::kPercent:
    case TokenKind::kPower:
      return EvalBinaryArith(op, lhs, rhs, arena);
    case TokenKind::kAmp:
    case TokenKind::kPipe:
    case TokenKind::kCaret:
      return EvalBinaryBitwise(op, lhs, rhs, arena);
    default:
      return EvalBinaryCompare(op, lhs, rhs, arena);
  }
}

// --- Compound assignment operators (§11.4.1) ---

static TokenKind CompoundAssignBaseOp(TokenKind op) {
  switch (op) {
    case TokenKind::kPlusEq:
      return TokenKind::kPlus;
    case TokenKind::kMinusEq:
      return TokenKind::kMinus;
    case TokenKind::kStarEq:
      return TokenKind::kStar;
    case TokenKind::kSlashEq:
      return TokenKind::kSlash;
    case TokenKind::kPercentEq:
      return TokenKind::kPercent;
    case TokenKind::kAmpEq:
      return TokenKind::kAmp;
    case TokenKind::kPipeEq:
      return TokenKind::kPipe;
    case TokenKind::kCaretEq:
      return TokenKind::kCaret;
    case TokenKind::kLtLtEq:
      return TokenKind::kLtLt;
    case TokenKind::kGtGtEq:
      return TokenKind::kGtGt;
    case TokenKind::kLtLtLtEq:
      return TokenKind::kLtLtLt;
    case TokenKind::kGtGtGtEq:
      return TokenKind::kGtGtGt;
    default:
      return TokenKind::kEof;
  }
}

static bool IsCompoundAssignOp(TokenKind op) {
  return CompoundAssignBaseOp(op) != TokenKind::kEof;
}

static Logic4Vec EvalCompoundAssign(const Expr* expr, SimContext& ctx,
                                    Arena& arena) {
  auto lhs_val = EvalExpr(expr->lhs, ctx, arena);
  auto rhs_val = EvalExpr(expr->rhs, ctx, arena);
  auto base_op = CompoundAssignBaseOp(expr->op);
  auto result = EvalBinaryOp(base_op, lhs_val, rhs_val, arena);
  if (expr->lhs->kind == ExprKind::kIdentifier) {
    auto* var = ctx.FindVariable(expr->lhs->text);
    if (var) var->value = result;
  }
  return result;
}

// --- Concatenation assembly (shared with eval_expr.cpp) ---

Logic4Vec AssembleConcatParts(const std::vector<Logic4Vec>& parts,
                              uint32_t total_width, Arena& arena) {
  auto result = MakeLogic4Vec(arena, total_width);
  uint32_t bit_pos = 0;
  for (auto it = parts.rbegin(); it != parts.rend(); ++it) {
    uint64_t val = it->ToUint64();
    uint32_t w = it->width;
    if (w > 64) w = 64;
    uint32_t word = bit_pos / 64;
    uint32_t bit = bit_pos % 64;
    if (word < result.nwords) {
      result.words[word].aval |= val << bit;
      if (bit + w > 64 && word + 1 < result.nwords) {
        result.words[word + 1].aval |= val >> (64 - bit);
      }
    }
    bit_pos += it->width;
  }
  return result;
}

// --- Concatenation ---

static Logic4Vec EvalConcat(const Expr* expr, SimContext& ctx, Arena& arena) {
  uint32_t total_width = 0;
  std::vector<Logic4Vec> parts;
  for (auto* elem : expr->elements) {
    parts.push_back(EvalExpr(elem, ctx, arena));
    total_width += parts.back().width;
  }
  if (total_width == 0) return MakeLogic4Vec(arena, 1);
  return AssembleConcatParts(parts, total_width, arena);
}

// --- Select (bit/part) ---

// §7.10: Resolve a queue index with $ = last element index.
static uint64_t ResolveQueueIdx(const Expr* idx_expr, QueueObject* q,
                                SimContext& ctx, Arena& arena) {
  ctx.PushScope();
  auto* dv = ctx.CreateLocalVariable("$", 32);
  uint64_t last = q->elements.empty() ? 0 : q->elements.size() - 1;
  dv->value = MakeLogic4VecVal(arena, 32, last);
  auto val = EvalExpr(idx_expr, ctx, arena);
  ctx.PopScope();
  return val.ToUint64();
}

// §7.10: Try queue indexed access with $ support. Returns true if handled.
static bool TryQueueSelect(const Expr* expr, SimContext& ctx, Arena& arena,
                           Logic4Vec& out) {
  if (!expr->base || expr->base->kind != ExprKind::kIdentifier) return false;
  if (expr->index_end) return false;
  auto* q = ctx.FindQueue(expr->base->text);
  if (!q) return false;
  auto idx = ResolveQueueIdx(expr->index, q, ctx, arena);
  out = (idx < q->elements.size()) ? q->elements[idx]
                                   : MakeLogic4VecVal(arena, q->elem_width, 0);
  return true;
}

// §7.4: Try unpacked array element access. Returns true if handled.
static bool TryArrayElementSelect(const Expr* expr, uint64_t idx,
                                  SimContext& ctx, Logic4Vec& out) {
  if (!expr->base || expr->base->kind != ExprKind::kIdentifier) return false;
  if (expr->index_end) return false;
  auto elem_name =
      std::string(expr->base->text) + "[" + std::to_string(idx) + "]";
  auto* elem = ctx.FindVariable(elem_name);
  if (!elem) return false;
  out = elem->value;
  return true;
}

// §7.4: Build a compound variable name from chained selects (e.g., mem[i][j]).
static bool BuildCompoundName(const Expr* expr, SimContext& ctx, Arena& arena,
                              std::string& name) {
  if (expr->kind == ExprKind::kIdentifier) {
    name = expr->text;
    return true;
  }
  if (expr->kind != ExprKind::kSelect || expr->index_end) return false;
  if (!BuildCompoundName(expr->base, ctx, arena, name)) return false;
  auto idx = EvalExpr(expr->index, ctx, arena).ToUint64();
  name += "[" + std::to_string(idx) + "]";
  return true;
}

// §7.4: Try multi-dimensional array element access (e.g., mem[i][j]).
static bool TryCompoundArraySelect(const Expr* expr, SimContext& ctx,
                                   Arena& arena, Logic4Vec& out) {
  if (!expr->base || expr->base->kind != ExprKind::kSelect) return false;
  if (expr->index_end) return false;
  std::string compound;
  if (!BuildCompoundName(expr, ctx, arena, compound)) return false;
  auto* elem = ctx.FindVariable(compound);
  if (!elem) return false;
  out = elem->value;
  return true;
}

// Evaluate a packed part-select: base[hi:lo].
static Logic4Vec EvalPartSelect(const Logic4Vec& base_val, uint64_t idx,
                                uint64_t end_idx, Arena& arena) {
  auto lo = static_cast<uint32_t>(std::min(idx, end_idx));
  auto hi = static_cast<uint32_t>(std::max(idx, end_idx));
  uint32_t width = hi - lo + 1;
  uint64_t val = base_val.ToUint64() >> lo;
  uint64_t mask = (width >= 64) ? ~uint64_t{0} : (uint64_t{1} << width) - 1;
  return MakeLogic4VecVal(arena, width, val & mask);
}

// §7.8: Return the default-or-zero value for an assoc array miss.
static Logic4Vec AssocDefault(const AssocArrayObject* aa, Arena& arena) {
  return aa->has_default ? aa->default_value
                         : MakeLogic4VecVal(arena, aa->elem_width, 0);
}

// §7.8: Extract string key from a Logic4Vec (packed byte representation).
static std::string ExtractStringKey(const Logic4Vec& key) {
  uint32_t nb = key.width / 8;
  std::string s;
  s.reserve(nb);
  for (uint32_t i = nb; i > 0; --i) {
    uint32_t bi = i - 1;
    auto ch = static_cast<char>(
        (key.words[(bi * 8) / 64].aval >> ((bi * 8) % 64)) & 0xFF);
    if (ch != 0) s.push_back(ch);
  }
  return s;
}

// §7.8.6: Read assoc array, returning value or default (with warning on miss).
static Logic4Vec AssocReadOrDefault(const AssocArrayObject* aa, bool found,
                                    Logic4Vec found_val,
                                    std::string_view arr_name, SimContext& ctx,
                                    Arena& arena) {
  if (found) return found_val;
  if (!aa->has_default)
    ctx.GetDiag().Warning({}, "associative array '" + std::string(arr_name) +
                                  "': read of non-existent index");
  return AssocDefault(aa, arena);
}

// §7.8: Read from assoc array by string key.
static Logic4Vec AssocReadStr(AssocArrayObject* aa, const Expr* idx_expr,
                              std::string_view name, SimContext& ctx,
                              Arena& arena) {
  auto s = ExtractStringKey(EvalExpr(idx_expr, ctx, arena));
  auto it = aa->str_data.find(s);
  bool hit = (it != aa->str_data.end());
  return AssocReadOrDefault(aa, hit, hit ? it->second : Logic4Vec{}, name, ctx,
                            arena);
}

// §7.8: Read from assoc array by integer key.
static Logic4Vec AssocReadInt(AssocArrayObject* aa, const Expr* idx_expr,
                              std::string_view name, SimContext& ctx,
                              Arena& arena) {
  auto key = static_cast<int64_t>(EvalExpr(idx_expr, ctx, arena).ToUint64());
  auto it = aa->int_data.find(key);
  bool hit = (it != aa->int_data.end());
  return AssocReadOrDefault(aa, hit, hit ? it->second : Logic4Vec{}, name, ctx,
                            arena);
}

// §7.8: Try associative array indexed access. Returns true if handled.
static bool TryAssocSelect(const Expr* expr, SimContext& ctx, Arena& arena,
                           Logic4Vec& out) {
  if (!expr->base || expr->base->kind != ExprKind::kIdentifier) return false;
  if (expr->index_end) return false;
  auto* aa = ctx.FindAssocArray(expr->base->text);
  if (!aa) return false;
  out = aa->is_string_key
            ? AssocReadStr(aa, expr->index, expr->base->text, ctx, arena)
            : AssocReadInt(aa, expr->index, expr->base->text, ctx, arena);
  return true;
}

static Logic4Vec EvalSelect(const Expr* expr, SimContext& ctx, Arena& arena) {
  Logic4Vec result;
  if (TryQueueSelect(expr, ctx, arena, result)) return result;
  if (TryAssocSelect(expr, ctx, arena, result)) return result;

  auto idx_val = EvalExpr(expr->index, ctx, arena);
  uint64_t idx = idx_val.ToUint64();

  if (TryArrayElementSelect(expr, idx, ctx, result)) return result;
  if (TryCompoundArraySelect(expr, ctx, arena, result)) return result;

  auto base_val = EvalExpr(expr->base, ctx, arena);
  if (expr->index_end) {
    auto end_val = EvalExpr(expr->index_end, ctx, arena).ToUint64();
    if (expr->is_part_select_plus) {
      // §7.4.5: base[idx +: width] → extract `width` bits from bit `idx`.
      auto w = static_cast<uint32_t>(end_val);
      return EvalPartSelect(base_val, idx, idx + w - 1, arena);
    }
    if (expr->is_part_select_minus) {
      // §7.4.5: base[idx -: width] → extract `width` bits ending at `idx`.
      auto w = static_cast<uint32_t>(end_val);
      uint64_t lo = (idx >= w - 1) ? idx - w + 1 : 0;
      return EvalPartSelect(base_val, lo, idx, arena);
    }
    return EvalPartSelect(base_val, idx, end_val, arena);
  }
  // Single bit select.
  return MakeLogic4VecVal(arena, 1, (base_val.ToUint64() >> idx) & 1);
}

// --- Ternary ---

static Logic4Vec EvalTernary(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto cond = EvalExpr(expr->condition, ctx, arena);
  if (cond.ToUint64() != 0) {
    return EvalExpr(expr->true_expr, ctx, arena);
  }
  return EvalExpr(expr->false_expr, ctx, arena);
}

// --- Binary expression with short-circuit ---

// §10.3: Assignment within expression — evaluate RHS, store in LHS, return.
static Logic4Vec EvalAssignInExpr(const Expr* expr, SimContext& ctx,
                                  Arena& arena) {
  auto rhs_val = EvalExpr(expr->rhs, ctx, arena);
  if (expr->lhs->kind == ExprKind::kIdentifier) {
    auto* var = ctx.FindVariable(expr->lhs->text);
    if (var) var->value = rhs_val;
  }
  return rhs_val;
}

static Logic4Vec EvalBinaryExpr(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  if (expr->op == TokenKind::kEq) return EvalAssignInExpr(expr, ctx, arena);
  if (expr->op == TokenKind::kAmpAmp) {
    auto l = EvalExpr(expr->lhs, ctx, arena);
    if (l.ToUint64() == 0) return MakeLogic4VecVal(arena, 1, 0);
    auto r = EvalExpr(expr->rhs, ctx, arena);
    return MakeLogic4VecVal(arena, 1, r.ToUint64() != 0 ? 1 : 0);
  }
  if (expr->op == TokenKind::kPipePipe) {
    auto l = EvalExpr(expr->lhs, ctx, arena);
    if (l.ToUint64() != 0) return MakeLogic4VecVal(arena, 1, 1);
    auto r = EvalExpr(expr->rhs, ctx, arena);
    return MakeLogic4VecVal(arena, 1, r.ToUint64() != 0 ? 1 : 0);
  }
  return EvalBinaryOp(expr->op, EvalExpr(expr->lhs, ctx, arena),
                      EvalExpr(expr->rhs, ctx, arena), arena);
}

// --- Main dispatch ---

Logic4Vec EvalExpr(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (!expr) return MakeLogic4Vec(arena, 1);

  switch (expr->kind) {
    case ExprKind::kIntegerLiteral:
      return EvalIntLiteral(expr, arena);
    case ExprKind::kUnbasedUnsizedLiteral:
      return EvalUnbasedUnsized(expr, arena);
    case ExprKind::kStringLiteral:
      return EvalStringLiteral(expr, arena);
    case ExprKind::kRealLiteral: {
      uint64_t bits = 0;
      std::memcpy(&bits, &expr->real_val, sizeof(double));
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
      return EvalBinaryExpr(expr, ctx, arena);
    case ExprKind::kTernary:
      return EvalTernary(expr, ctx, arena);
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
    default:
      return MakeLogic4Vec(arena, 1);
  }
}

}  // namespace delta
