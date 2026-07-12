#include "elaborator/const_eval.h"

#include <cmath>
#include <cstring>
#include <unordered_set>

#include "lexer/token.h"
#include "parser/ast.h"

namespace delta {

static std::optional<int64_t> EvalPower(int64_t base, int64_t exp) {
  if (exp < 0) {
    if (base == 0) return std::nullopt;
    if (base == 1) return 1;
    if (base == -1) return (exp % 2 == 0) ? 1 : -1;
    return 0;
  }
  int64_t result = 1;
  for (int64_t i = 0; i < exp; ++i) {
    result *= base;
  }
  return result;
}

static std::optional<int64_t> EvalBinaryArith(TokenKind op, int64_t lhs,
                                              int64_t rhs) {
  switch (op) {
    case TokenKind::kPlus:
    case TokenKind::kPlusEq:
      return lhs + rhs;
    case TokenKind::kMinus:
    case TokenKind::kMinusEq:
      return lhs - rhs;
    case TokenKind::kStar:
    case TokenKind::kStarEq:
      return lhs * rhs;
    case TokenKind::kSlash:
    case TokenKind::kSlashEq:
      if (rhs == 0) return std::nullopt;
      return lhs / rhs;
    case TokenKind::kPercent:
    case TokenKind::kPercentEq:
      if (rhs == 0) return std::nullopt;
      return lhs % rhs;
    case TokenKind::kPower:
      return EvalPower(lhs, rhs);
    default:
      return std::nullopt;
  }
}

static std::optional<int64_t> EvalBinaryBitwise(TokenKind op, int64_t lhs,
                                                int64_t rhs) {
  switch (op) {
    case TokenKind::kAmp:
    case TokenKind::kAmpEq:
      return lhs & rhs;
    case TokenKind::kPipe:
    case TokenKind::kPipeEq:
      return lhs | rhs;
    case TokenKind::kCaret:
    case TokenKind::kCaretEq:
      return lhs ^ rhs;
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
      return ~(lhs ^ rhs);
    case TokenKind::kLtLt:
    case TokenKind::kLtLtLt:
    case TokenKind::kLtLtEq:
    case TokenKind::kLtLtLtEq:
      return lhs << rhs;
    case TokenKind::kGtGt:
    case TokenKind::kGtGtEq:
      return static_cast<int64_t>(static_cast<uint64_t>(lhs) >> rhs);
    case TokenKind::kGtGtGt:
    case TokenKind::kGtGtGtEq:
      return lhs >> rhs;
    default:
      return std::nullopt;
  }
}

static std::optional<int64_t> EvalBinaryCompare(TokenKind op, int64_t lhs,
                                                int64_t rhs) {
  switch (op) {
    case TokenKind::kLt:
      return static_cast<int64_t>(lhs < rhs);
    case TokenKind::kGt:
      return static_cast<int64_t>(lhs > rhs);
    case TokenKind::kLtEq:
      return static_cast<int64_t>(lhs <= rhs);
    case TokenKind::kGtEq:
      return static_cast<int64_t>(lhs >= rhs);
    case TokenKind::kEqEq:
      return static_cast<int64_t>(lhs == rhs);
    case TokenKind::kBangEq:
      return static_cast<int64_t>(lhs != rhs);
    case TokenKind::kAmpAmp:
      return static_cast<int64_t>(lhs != 0 && rhs != 0);
    case TokenKind::kPipePipe:
      return static_cast<int64_t>(lhs != 0 || rhs != 0);
    case TokenKind::kArrow:
      return static_cast<int64_t>(lhs == 0 || rhs != 0);
    case TokenKind::kLtDashGt:
      return static_cast<int64_t>((lhs != 0) == (rhs != 0));
    default:
      return std::nullopt;
  }
}

static std::optional<int64_t> EvalBinary(TokenKind op, int64_t lhs,
                                         int64_t rhs) {
  auto result = EvalBinaryArith(op, lhs, rhs);
  if (result) return result;
  result = EvalBinaryBitwise(op, lhs, rhs);
  if (result) return result;
  return EvalBinaryCompare(op, lhs, rhs);
}

static std::optional<int64_t> EvalUnary(TokenKind op, int64_t operand) {
  switch (op) {
    case TokenKind::kMinus:
      return -operand;
    case TokenKind::kPlus:
      return operand;
    case TokenKind::kTilde:
      return ~operand;
    case TokenKind::kBang:
      return operand == 0 ? 1 : 0;
    default:
      return std::nullopt;
  }
}

static uint32_t ConstLiteralWidth(const Expr* expr) {
  auto tick = expr->text.find('\'');
  if (tick != std::string_view::npos && tick > 0) {
    uint32_t w = 0;
    for (size_t i = 0; i < tick; ++i) {
      char c = expr->text[i];
      if (c >= '0' && c <= '9') w = w * 10 + (c - '0');
    }
    if (w > 0) return w;
  }
  return 32;
}

static int64_t Clog2(int64_t val) {
  // The argument is treated as an unsigned value, so reinterpret the bit
  // pattern as unsigned rather than special-casing negative inputs. An
  // argument of 0 (or 1) yields 0.
  auto v = static_cast<uint64_t>(val);
  if (v <= 1) return 0;
  int64_t result = 0;
  uint64_t shifted = v - 1;
  while (shifted > 0) {
    shifted >>= 1;
    ++result;
  }
  return result;
}

static std::optional<int64_t> EvalConcat(const Expr* expr,
                                         const ScopeMap& scope) {
  int64_t result = 0;
  for (auto* elem : expr->elements) {
    auto val = ConstEvalInt(elem, scope);
    if (!val) return std::nullopt;
    uint32_t w = ConstLiteralWidth(elem);
    result = (result << w) | (*val & ((int64_t{1} << w) - 1));
  }
  return result;
}

static std::optional<int64_t> EvalReplicate(const Expr* expr,
                                            const ScopeMap& scope) {
  auto count = ConstEvalInt(expr->repeat_count, scope);
  if (!count || expr->elements.empty()) return std::nullopt;
  auto val = ConstEvalInt(expr->elements[0], scope);
  if (!val) return std::nullopt;
  uint32_t w = ConstLiteralWidth(expr->elements[0]);
  int64_t result = 0;
  for (int64_t i = 0; i < *count; ++i) {
    result = (result << w) | (*val & ((int64_t{1} << w) - 1));
  }
  return result;
}

static int64_t Countones(int64_t val) {
  auto u = static_cast<uint64_t>(val);
  int64_t count = 0;
  while (u != 0) {
    u &= u - 1;
    ++count;
  }
  return count;
}

static std::optional<int64_t> EvalFirstArg(const Expr* expr,
                                           const ScopeMap& scope) {
  if (expr->args.empty()) return std::nullopt;
  return ConstEvalInt(expr->args[0], scope);
}

// §20.6.2: the packed bit width of a built-in integral type keyword. The
// vector atoms (bit/logic/reg) are 1 bit; the integer-atom keywords carry
// their standard widths. Non-integral (real, string, ...) and user-defined
// types are not sized here.
static std::optional<int64_t> IntegralKeywordWidth(std::string_view kw) {
  if (kw == "bit" || kw == "logic" || kw == "reg") return 1;
  if (kw == "byte") return 8;
  if (kw == "shortint") return 16;
  if (kw == "int" || kw == "integer") return 32;
  if (kw == "longint" || kw == "time") return 64;
  return std::nullopt;
}

// §20.6.2: fold $bits on a fixed-size argument to a constant at elaboration.
// An integer literal contributes its declared width. A built-in data type --
// a bare keyword (int, logic, ...) or a ranged vector (logic [7:0]) -- has a
// width knowable from the argument syntax alone, so it folds here as well; the
// ranged form multiplies the atom width by the packed range. User-defined type
// names and typed expressions need type/instance resolution unavailable at this
// layer and are left to be sized at run time.
static std::optional<int64_t> EvalConstBits(const Expr* expr,
                                            const ScopeMap& scope) {
  if (expr->args.empty()) return std::nullopt;
  auto* a = expr->args[0];
  if (a->kind == ExprKind::kIntegerLiteral)
    return static_cast<int64_t>(ConstLiteralWidth(a));

  if (a->kind == ExprKind::kIdentifier) {
    if (auto w = IntegralKeywordWidth(a->text)) return *w;
  }
  if (a->kind == ExprKind::kSelect && a->index && a->index_end &&
      !a->is_part_select_plus && !a->is_part_select_minus && a->base &&
      a->base->kind == ExprKind::kIdentifier) {
    if (auto atom = IntegralKeywordWidth(a->base->text)) {
      auto hi = ConstEvalInt(a->index, scope);
      auto lo = ConstEvalInt(a->index_end, scope);
      if (hi && lo) {
        int64_t span = (*hi >= *lo ? *hi - *lo : *lo - *hi) + 1;
        return *atom * span;
      }
    }
  }
  return std::nullopt;
}

// A control_bit text starting with `'` (or sized as N'...) carries x or z if
// any digit character following the base specifier is x/z/?. Constant integer
// expressions contain no x or z bits, so x/z control_bits contribute zero.
static bool ControlBitIsXZ(const Expr* ctrl) {
  if (!ctrl || ctrl->kind != ExprKind::kIntegerLiteral) return false;
  auto t = ctrl->text;
  auto tick = t.find('\'');
  if (tick == std::string_view::npos) return false;
  for (size_t i = tick + 1; i < t.size(); ++i) {
    char c = t[i];
    if (c == 'x' || c == 'X' || c == 'z' || c == 'Z' || c == '?') return true;
  }
  return false;
}

static int64_t CountonesInWidth(int64_t val, uint32_t width) {
  uint64_t mask =
      (width == 0 || width >= 64) ? ~uint64_t{0} : ((uint64_t{1} << width) - 1);
  return Countones(static_cast<int64_t>(static_cast<uint64_t>(val) & mask));
}

static std::optional<int64_t> EvalConstCountbits(const Expr* expr,
                                                 const ScopeMap& scope) {
  if (expr->args.size() < 2) return std::nullopt;
  auto val = ConstEvalInt(expr->args[0], scope);
  if (!val) return std::nullopt;
  uint32_t width = ConstLiteralWidth(expr->args[0]);
  bool match0 = false;
  bool match1 = false;
  for (size_t i = 1; i < expr->args.size(); ++i) {
    auto* ctrl = expr->args[i];
    if (ControlBitIsXZ(ctrl)) continue;
    auto cb = ConstEvalInt(ctrl, scope);
    if (!cb) return std::nullopt;
    // Only the LSB of the control_bit is examined (§20.9). Duplicates collapse
    // because match0/match1 are idempotent boolean sets.
    if ((*cb & 1) == 0) {
      match0 = true;
    } else {
      match1 = true;
    }
  }
  int64_t ones = CountonesInWidth(*val, width);
  int64_t total = (width >= 64) ? 64 : static_cast<int64_t>(width);
  int64_t zeros = total - ones;
  int64_t result = 0;
  if (match1) result += ones;
  if (match0) result += zeros;
  return result;
}

static std::optional<int64_t> EvalConstSysCall(const Expr* expr,
                                               const ScopeMap& scope) {
  if (expr->callee == "$bits") return EvalConstBits(expr, scope);
  if (expr->callee == "$countbits") return EvalConstCountbits(expr, scope);
  // §20.5: the integer-returning conversion functions take a real argument, so
  // they fold from the constant real value rather than an integral first arg.
  if (expr->callee == "$rtoi" || expr->callee == "$realtobits" ||
      expr->callee == "$shortrealtobits") {
    if (expr->args.empty()) return std::nullopt;
    auto rv = ConstEvalReal(expr->args[0], scope);
    if (!rv) return std::nullopt;
    if (expr->callee == "$rtoi")
      return static_cast<int64_t>(*rv);  // truncates toward zero
    if (expr->callee == "$realtobits") {
      double d = *rv;
      uint64_t bits = 0;
      std::memcpy(&bits, &d, sizeof(d));
      return static_cast<int64_t>(bits);
    }
    // $shortrealtobits: narrow to single precision, reinterpret the 32 bits.
    float fv = static_cast<float>(*rv);
    uint32_t bits = 0;
    std::memcpy(&bits, &fv, sizeof(fv));
    return static_cast<int64_t>(bits);
  }
  auto arg = EvalFirstArg(expr, scope);
  if (!arg) return std::nullopt;
  if (expr->callee == "$clog2") return Clog2(*arg);
  if (expr->callee == "$countones") return Countones(*arg);
  if (expr->callee == "$onehot")
    return static_cast<int64_t>(Countones(*arg) == 1);
  if (expr->callee == "$onehot0")
    return static_cast<int64_t>(Countones(*arg) <= 1);
  // A constant-expression argument has no x or z bits by definition, so
  // $isunknown of a constant expression is always 0.
  if (expr->callee == "$isunknown") return 0;
  return std::nullopt;
}

struct ConstVal {
  int64_t value;
  uint32_t width;
  bool is_signed;
};

static bool IsSignedLiteral(std::string_view text) {
  auto tick = text.find('\'');
  if (tick == std::string_view::npos) return true;
  if (tick + 1 >= text.size()) return false;
  char c = text[tick + 1];
  return c == 's' || c == 'S';
}

static int64_t TruncateToWidth(int64_t val, uint32_t width) {
  if (width == 0 || width >= 64) return val;
  return static_cast<int64_t>(static_cast<uint64_t>(val) &
                              ((uint64_t{1} << width) - 1));
}

static int64_t SignExtendFromWidth(int64_t val, uint32_t width) {
  if (width == 0 || width >= 64) return val;
  uint64_t mask = (uint64_t{1} << width) - 1;
  uint64_t uval = static_cast<uint64_t>(val) & mask;
  if (uval & (uint64_t{1} << (width - 1))) {
    uval |= ~mask;
  }
  return static_cast<int64_t>(uval);
}

static std::optional<ConstVal> ConstEvalFull(const Expr* expr,
                                             const ScopeMap& scope);

static std::optional<ConstVal> ConstEvalLiteral(const Expr* expr) {
  uint32_t w = ConstLiteralWidth(expr);
  bool s = IsSignedLiteral(expr->text);
  int64_t v = TruncateToWidth(static_cast<int64_t>(expr->int_val), w);
  if (s) v = SignExtendFromWidth(v, w);
  return ConstVal{v, w, s};
}

static int ConstHexDigitVal(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}

// Decodes one backslash escape starting at text[i] (i points at the char after
// the backslash) into a byte, advancing i past the consumed characters. Mirrors
// the simulator's string-literal decoding so a literal folded here matches the
// value produced at run time.
static bool ConstDecodeEscape(std::string_view text, size_t& i, uint8_t& out) {
  char c = text[i];
  switch (c) {
    case 'n':
      out = '\n';
      return true;
    case 't':
      out = '\t';
      return true;
    case '\\':
      out = '\\';
      return true;
    case '"':
      out = '"';
      return true;
    case 'v':
      out = '\v';
      return true;
    case 'f':
      out = '\f';
      return true;
    case 'a':
      out = '\a';
      return true;
    default:
      break;
  }
  if (c == '\n') return false;  // line continuation: emit nothing
  if (c == 'x') {
    uint8_t val = 0;
    for (int j = 0; j < 2 && i + 1 < text.size(); ++j) {
      int d = ConstHexDigitVal(text[i + 1]);
      if (d < 0) break;
      val = static_cast<uint8_t>(val * 16 + d);
      ++i;
    }
    out = val;
    return true;
  }
  if (c >= '0' && c <= '7') {
    auto val = static_cast<uint8_t>(c - '0');
    for (int j = 0; j < 2 && i + 1 < text.size() && text[i + 1] >= '0' &&
                    text[i + 1] <= '7';
         ++j) {
      val = static_cast<uint8_t>(val * 8 + (text[++i] - '0'));
    }
    out = val;
    return true;
  }
  out = static_cast<uint8_t>(c);
  return true;
}

// §11.10: a string literal operand is a constant number formed from the 8-bit
// ASCII code of each character, one byte per character, packed with the first
// character in the most-significant position. This lets a string literal fold
// in constant expressions (e.g. a parameter/localparam initializer). The folded
// value keeps the low 64 bits, matching the low word of the equivalent vector.
static std::optional<ConstVal> ConstEvalStringLiteral(const Expr* expr) {
  std::string_view text = expr->text;
  if (text.size() >= 6 && text.substr(0, 3) == "\"\"\"")
    text = text.substr(3, text.size() - 6);
  else if (text.size() >= 2 && text.front() == '"')
    text = text.substr(1, text.size() - 2);

  uint64_t value = 0;
  uint32_t nbytes = 0;
  for (size_t i = 0; i < text.size(); ++i) {
    uint8_t byte = 0;
    if (text[i] == '\\' && i + 1 < text.size()) {
      ++i;
      if (!ConstDecodeEscape(text, i, byte)) continue;  // line continuation
    } else {
      byte = static_cast<uint8_t>(text[i]);
    }
    value = (value << 8) | byte;
    ++nbytes;
  }
  uint32_t width = nbytes == 0 ? 8u : nbytes * 8u;
  return ConstVal{static_cast<int64_t>(value), width, false};
}

static std::optional<ConstVal> ConstEvalUnaryFull(const Expr* expr,
                                                  const ScopeMap& scope) {
  auto operand = ConstEvalFull(expr->lhs, scope);
  if (!operand) return std::nullopt;
  if (expr->op == TokenKind::kMinus) {
    int64_t v = TruncateToWidth(-operand->value, operand->width);
    if (operand->is_signed) v = SignExtendFromWidth(v, operand->width);
    return ConstVal{v, operand->width, operand->is_signed};
  }
  auto result = EvalUnary(expr->op, operand->value);
  if (!result) return std::nullopt;
  int64_t v = TruncateToWidth(*result, operand->width);
  if (operand->is_signed) v = SignExtendFromWidth(v, operand->width);
  return ConstVal{v, operand->width, operand->is_signed};
}

// Normalizes the binary operands to their effective signed/unsigned values:
// signed operands are sign-extended from their declared width, unsigned
// operands are truncated to their declared width.
static void NormalizeBinaryOperands(const ConstVal& lhs, const ConstVal& rhs,
                                    bool is_signed, int64_t& lv, int64_t& rv) {
  if (is_signed) {
    lv = SignExtendFromWidth(lhs.value, lhs.width);
    rv = SignExtendFromWidth(rhs.value, rhs.width);
  } else {
    lv = TruncateToWidth(lhs.value, lhs.width);
    rv = TruncateToWidth(rhs.value, rhs.width);
  }
}

// Handles unsigned division and modulo, which require unsigned arithmetic on
// the operands. Returns std::nullopt for non-div/mod operators (signaling the
// caller to fall through to the generic signed evaluator) and on
// divide-by-zero. The has_result output distinguishes "not a div/mod op" from a
// real failure.
static std::optional<ConstVal> EvalUnsignedDivMod(TokenKind op, int64_t lv,
                                                  int64_t rv, uint32_t width,
                                                  bool& handled) {
  handled = true;
  auto ul = static_cast<uint64_t>(lv);
  auto ur = static_cast<uint64_t>(rv);
  if (op == TokenKind::kSlash || op == TokenKind::kSlashEq) {
    if (ur == 0) return std::nullopt;
    return ConstVal{static_cast<int64_t>(ul / ur), width, false};
  }
  if (op == TokenKind::kPercent || op == TokenKind::kPercentEq) {
    if (ur == 0) return std::nullopt;
    return ConstVal{static_cast<int64_t>(ul % ur), width, false};
  }
  handled = false;
  return std::nullopt;
}

static std::optional<ConstVal> ConstEvalBinaryFull(const Expr* expr,
                                                   const ScopeMap& scope) {
  auto lhs = ConstEvalFull(expr->lhs, scope);
  auto rhs = ConstEvalFull(expr->rhs, scope);
  if (!lhs || !rhs) return std::nullopt;
  uint32_t w = std::max(lhs->width, rhs->width);
  bool s = lhs->is_signed && rhs->is_signed;
  int64_t lv = 0, rv = 0;
  NormalizeBinaryOperands(*lhs, *rhs, s, lv, rv);
  if (!s) {
    bool handled = false;
    auto div_result = EvalUnsignedDivMod(expr->op, lv, rv, w, handled);
    if (handled) return div_result;
  }
  auto result = EvalBinary(expr->op, lv, rv);
  if (!result) return std::nullopt;
  int64_t v = TruncateToWidth(*result, w);
  // §11.4.10: the logical right shift (>>) zero-fills vacated high bits, so its
  // result is never sign-extended even when the operand type is signed. Only
  // arithmetic results (incl. the arithmetic right shift >>>) propagate the
  // sign bit.
  bool is_logical_rshift =
      expr->op == TokenKind::kGtGt || expr->op == TokenKind::kGtGtEq;
  if (s && !is_logical_rshift) v = SignExtendFromWidth(v, w);
  return ConstVal{v, w, s};
}

static std::optional<ConstVal> ConstEvalSelectFull(const Expr* expr,
                                                   const ScopeMap& scope) {
  auto base_val = ConstEvalFull(expr->base, scope);
  if (!base_val) return std::nullopt;
  auto idx = ConstEvalFull(expr->index, scope);
  if (!idx) return std::nullopt;
  if (expr->index_end) {
    auto end = ConstEvalFull(expr->index_end, scope);
    if (!end) return std::nullopt;
    int64_t hi = std::max(idx->value, end->value);
    int64_t lo = std::min(idx->value, end->value);
    int64_t width = hi - lo + 1;
    if (width <= 0 || width > 63) return std::nullopt;
    int64_t v = (base_val->value >> lo) & ((int64_t{1} << width) - 1);
    return ConstVal{v, static_cast<uint32_t>(width), false};
  }
  return ConstVal{(base_val->value >> idx->value) & 1, 1, false};
}

static std::optional<ConstVal> ConstEvalSysCallFull(const Expr* expr,
                                                    const ScopeMap& scope) {
  if (expr->callee == "$signed" || expr->callee == "$unsigned") {
    if (expr->args.empty()) return std::nullopt;
    auto arg = ConstEvalFull(expr->args[0], scope);
    if (!arg) return std::nullopt;
    return ConstVal{arg->value, arg->width, expr->callee == "$signed"};
  }
  auto val = EvalConstSysCall(expr, scope);
  if (!val) return std::nullopt;
  return ConstVal{*val, 32, true};
}

// §8.25.1: registry of parameterized-class declarations visible to the constant
// folder, installed by the elaborator via ParamClassRegistryGuard. Null unless
// a guard is live. Used to map an accessed value-parameter name to its port
// position when resolving a specialization override.
static const std::unordered_map<std::string_view, const ClassDecl*>*
    g_param_class_registry = nullptr;

ParamClassRegistryGuard::ParamClassRegistryGuard(
    const std::unordered_map<std::string_view, const ClassDecl*>* classes)
    : prev_(g_param_class_registry) {
  g_param_class_registry = classes;
}

ParamClassRegistryGuard::~ParamClassRegistryGuard() {
  g_param_class_registry = prev_;
}

// §8.25.1: when a member access is `C#(args)::name` and `name` is one of class
// C's value parameter ports, fold to that specialization's override for `name`
// rather than the class default. Matches a named override (`.name(value)`)
// first, then an ordered override occupying the parameter's port position. Type
// parameters and body-local parameters are not overridable through #(...) and
// are left to the ordinary "Class.name" default lookup.
static std::optional<ConstVal> ConstEvalSpecializationOverride(
    const Expr* expr, const ScopeMap& scope) {
  if (!g_param_class_registry) return std::nullopt;
  const Expr* base = expr->lhs;
  if (!base || base->kind != ExprKind::kIdentifier || !base->has_param_spec ||
      base->elements.empty())
    return std::nullopt;
  if (!expr->rhs || expr->rhs->kind != ExprKind::kIdentifier)
    return std::nullopt;
  auto cit = g_param_class_registry->find(base->text);
  if (cit == g_param_class_registry->end() || cit->second == nullptr)
    return std::nullopt;
  const ClassDecl* decl = cit->second;
  size_t pos = decl->params.size();
  for (size_t i = 0; i < decl->params.size(); ++i) {
    if (decl->params[i].first == expr->rhs->text) {
      pos = i;
      break;
    }
  }
  if (pos == decl->params.size()) return std::nullopt;
  if (decl->type_param_names.count(expr->rhs->text)) return std::nullopt;
  const auto& elems = base->elements;
  const auto& names = base->arg_names;
  for (size_t j = 0; j < elems.size(); ++j) {
    if (j < names.size() && !names[j].empty() && names[j] == expr->rhs->text &&
        elems[j]) {
      return ConstEvalFull(elems[j], scope);
    }
  }
  bool ordered = names.empty() || (pos < names.size() && names[pos].empty());
  if (ordered && pos < elems.size() && elems[pos]) {
    return ConstEvalFull(elems[pos], scope);
  }
  return std::nullopt;
}

static std::optional<ConstVal> ConstEvalMemberAccessFull(
    const Expr* expr, const ScopeMap& scope) {
  if (auto override_val = ConstEvalSpecializationOverride(expr, scope))
    return override_val;
  if (expr->lhs && expr->rhs && expr->lhs->kind == ExprKind::kIdentifier &&
      expr->rhs->kind == ExprKind::kIdentifier) {
    std::string compound =
        std::string(expr->lhs->text) + "." + std::string(expr->rhs->text);
    auto it = scope.find(compound);
    if (it != scope.end()) return ConstVal{it->second, 32, true};
  }
  return std::nullopt;
}

// §13.4.3 constant-function-call evaluation ---------------------------------
//
// A constant function is a normal function evaluated at elaboration time so
// that e.g. `localparam addr_width = clogb2(ram_depth)` folds to an integer.
// The registry below is the set of user function declarations visible to the
// design element whose parameters are currently being resolved; it is null
// unless a ConstFuncRegistryGuard is live.
static const std::unordered_map<std::string_view, const ModuleItem*>*
    g_const_func_registry = nullptr;

// Bounds against pathological or (mutually) recursive constant functions:
// depth caps recursion, and each active call carries an iteration budget for
// its loops. Exhausting either simply abandons the fold (returns nullopt),
// leaving the parameter unresolved exactly as before this feature existed —
// never an error and never a wrong value.
static constexpr int kMaxConstFuncDepth = 64;
static constexpr int64_t kMaxConstFuncIterations = 10'000'000;
static int g_const_func_depth = 0;

ConstFuncRegistryGuard::ConstFuncRegistryGuard(
    const std::unordered_map<std::string_view, const ModuleItem*>* funcs)
    : prev_(g_const_func_registry) {
  g_const_func_registry = funcs;
}

ConstFuncRegistryGuard::~ConstFuncRegistryGuard() {
  g_const_func_registry = prev_;
}

// Control-flow outcome of interpreting one constant-function statement.
enum class ConstFuncFlow { kNormal, kReturn, kBreak, kContinue, kAbort };

static ConstFuncFlow ExecConstFuncStmt(const Stmt* s, ScopeMap& locals,
                                       std::string_view result_name,
                                       int64_t& iter_budget);

// A constant function may only assign to a simple (unindexed) local — its
// arguments, body-declared variables, or the implicit result variable named
// after the function. Anything else abandons the fold.
static bool ConstFuncAssign(const Expr* lhs, int64_t value, ScopeMap& locals) {
  if (!lhs || lhs->kind != ExprKind::kIdentifier || lhs->text.empty())
    return false;
  locals[lhs->text] = value;
  return true;
}

static ConstFuncFlow ExecConstFuncStmts(const std::vector<Stmt*>& stmts,
                                        ScopeMap& locals,
                                        std::string_view result_name,
                                        int64_t& iter_budget) {
  for (auto* s : stmts) {
    ConstFuncFlow flow = ExecConstFuncStmt(s, locals, result_name, iter_budget);
    if (flow != ConstFuncFlow::kNormal) return flow;
  }
  return ConstFuncFlow::kNormal;
}

static ConstFuncFlow ExecConstFuncStmt(const Stmt* s, ScopeMap& locals,
                                       std::string_view result_name,
                                       int64_t& iter_budget) {
  if (!s) return ConstFuncFlow::kNormal;
  switch (s->kind) {
    case StmtKind::kNull:
      return ConstFuncFlow::kNormal;
    case StmtKind::kBlock:
      return ExecConstFuncStmts(s->stmts, locals, result_name, iter_budget);
    case StmtKind::kVarDecl:
    case StmtKind::kBlockItemDecl: {
      // §13.4.3: body-local variables initialize as they would for normal
      // simulation. Model that as a fresh binding, seeded from the initializer
      // when one is present and 0 otherwise.
      if (s->var_name.empty()) return ConstFuncFlow::kNormal;
      int64_t init = 0;
      if (s->var_init) {
        auto v = ConstEvalFull(s->var_init, locals);
        if (!v) return ConstFuncFlow::kAbort;
        init = v->value;
      }
      locals[s->var_name] = init;
      return ConstFuncFlow::kNormal;
    }
    case StmtKind::kBlockingAssign: {
      if (!s->rhs) return ConstFuncFlow::kAbort;
      auto v = ConstEvalFull(s->rhs, locals);
      if (!v) return ConstFuncFlow::kAbort;
      if (!ConstFuncAssign(s->lhs, v->value, locals))
        return ConstFuncFlow::kAbort;
      return ConstFuncFlow::kNormal;
    }
    case StmtKind::kIf: {
      auto cond = ConstEvalFull(s->condition, locals);
      if (!cond) return ConstFuncFlow::kAbort;
      if (cond->value)
        return ExecConstFuncStmt(s->then_branch, locals, result_name,
                                 iter_budget);
      return ExecConstFuncStmt(s->else_branch, locals, result_name,
                               iter_budget);
    }
    case StmtKind::kFor: {
      ConstFuncFlow init_flow =
          ExecConstFuncStmts(s->for_inits, locals, result_name, iter_budget);
      if (init_flow == ConstFuncFlow::kAbort) return ConstFuncFlow::kAbort;
      while (true) {
        if (--iter_budget < 0) return ConstFuncFlow::kAbort;
        if (s->for_cond) {
          auto cond = ConstEvalFull(s->for_cond, locals);
          if (!cond) return ConstFuncFlow::kAbort;
          if (!cond->value) break;
        }
        ConstFuncFlow body =
            ExecConstFuncStmt(s->for_body, locals, result_name, iter_budget);
        if (body == ConstFuncFlow::kReturn || body == ConstFuncFlow::kAbort)
          return body;
        if (body == ConstFuncFlow::kBreak) break;
        ConstFuncFlow step =
            ExecConstFuncStmts(s->for_steps, locals, result_name, iter_budget);
        if (step == ConstFuncFlow::kAbort) return ConstFuncFlow::kAbort;
      }
      return ConstFuncFlow::kNormal;
    }
    case StmtKind::kWhile: {
      while (true) {
        if (--iter_budget < 0) return ConstFuncFlow::kAbort;
        auto cond = ConstEvalFull(s->condition, locals);
        if (!cond) return ConstFuncFlow::kAbort;
        if (!cond->value) break;
        ConstFuncFlow body =
            ExecConstFuncStmt(s->body, locals, result_name, iter_budget);
        if (body == ConstFuncFlow::kReturn || body == ConstFuncFlow::kAbort)
          return body;
        if (body == ConstFuncFlow::kBreak) break;
      }
      return ConstFuncFlow::kNormal;
    }
    case StmtKind::kDoWhile: {
      while (true) {
        if (--iter_budget < 0) return ConstFuncFlow::kAbort;
        ConstFuncFlow body =
            ExecConstFuncStmt(s->body, locals, result_name, iter_budget);
        if (body == ConstFuncFlow::kReturn || body == ConstFuncFlow::kAbort)
          return body;
        if (body == ConstFuncFlow::kBreak) break;
        auto cond = ConstEvalFull(s->condition, locals);
        if (!cond) return ConstFuncFlow::kAbort;
        if (!cond->value) break;
      }
      return ConstFuncFlow::kNormal;
    }
    case StmtKind::kRepeat: {
      auto count = ConstEvalFull(s->condition, locals);
      if (!count) return ConstFuncFlow::kAbort;
      for (int64_t i = 0; i < count->value; ++i) {
        if (--iter_budget < 0) return ConstFuncFlow::kAbort;
        ConstFuncFlow body =
            ExecConstFuncStmt(s->body, locals, result_name, iter_budget);
        if (body == ConstFuncFlow::kReturn || body == ConstFuncFlow::kAbort)
          return body;
        if (body == ConstFuncFlow::kBreak) break;
      }
      return ConstFuncFlow::kNormal;
    }
    case StmtKind::kReturn: {
      if (s->expr) {
        auto v = ConstEvalFull(s->expr, locals);
        if (!v) return ConstFuncFlow::kAbort;
        if (!result_name.empty()) locals[result_name] = v->value;
      }
      return ConstFuncFlow::kReturn;
    }
    case StmtKind::kBreak:
      return ConstFuncFlow::kBreak;
    case StmtKind::kContinue:
      return ConstFuncFlow::kContinue;
    case StmtKind::kExprStmt: {
      // §13.4.3: system task calls in a constant function are ignored (the
      // elaboration severity tasks of §20.10.1 are handled elsewhere). Other
      // bare expression statements — a pre/post increment on a local, say — are
      // interpreted for their side effect; anything else abandons the fold.
      const Expr* e = s->expr;
      if (!e) return ConstFuncFlow::kNormal;
      if (e->kind == ExprKind::kSystemCall) return ConstFuncFlow::kNormal;
      if ((e->kind == ExprKind::kPostfixUnary || e->kind == ExprKind::kUnary) &&
          e->lhs && e->lhs->kind == ExprKind::kIdentifier &&
          (e->op == TokenKind::kPlusPlus || e->op == TokenKind::kMinusMinus)) {
        auto cur = ConstEvalFull(e->lhs, locals);
        if (!cur) return ConstFuncFlow::kAbort;
        int64_t nv =
            e->op == TokenKind::kPlusPlus ? cur->value + 1 : cur->value - 1;
        locals[e->lhs->text] = nv;
        return ConstFuncFlow::kNormal;
      }
      return ConstFuncFlow::kAbort;
    }
    default:
      return ConstFuncFlow::kAbort;
  }
}

// §13.4.3: fold a call to a user-defined constant function. Returns nullopt
// (leaving the surrounding constant expression unresolved) whenever the callee
// is not a registered user function, an argument is not itself constant, or the
// body uses a construct the elaboration-time interpreter does not model.
static std::optional<ConstVal> ConstEvalUserCall(const Expr* expr,
                                                 const ScopeMap& scope) {
  if (!g_const_func_registry || expr->callee.empty()) return std::nullopt;
  auto it = g_const_func_registry->find(expr->callee);
  if (it == g_const_func_registry->end() || it->second == nullptr)
    return std::nullopt;
  const ModuleItem* func = it->second;
  if (func->kind != ModuleItemKind::kFunctionDecl) return std::nullopt;
  if (g_const_func_depth >= kMaxConstFuncDepth) return std::nullopt;
  ++g_const_func_depth;
  struct DepthGuard {
    ~DepthGuard() { --g_const_func_depth; }
  } depth_guard;

  // The body sees the caller's parameter scope (a constant function may
  // reference module/package/$unit parameters, §13.4.3), overlaid with the
  // argument bindings and the implicit result variable.
  ScopeMap locals = scope;
  for (size_t i = 0; i < func->func_args.size(); ++i) {
    const FunctionArg& fa = func->func_args[i];
    const Expr* arg_expr =
        i < expr->args.size() ? expr->args[i] : fa.default_value;
    if (!arg_expr) return std::nullopt;
    auto v = ConstEvalFull(arg_expr, scope);
    if (!v) return std::nullopt;
    if (!fa.name.empty()) locals[fa.name] = v->value;
  }
  if (!func->name.empty()) locals[func->name] = 0;

  int64_t iter_budget = kMaxConstFuncIterations;
  for (auto* s : func->func_body_stmts) {
    ConstFuncFlow flow = ExecConstFuncStmt(s, locals, func->name, iter_budget);
    if (flow == ConstFuncFlow::kAbort) return std::nullopt;
    if (flow == ConstFuncFlow::kReturn) break;
  }
  auto rit = locals.find(func->name);
  if (rit == locals.end()) return std::nullopt;
  return ConstVal{rit->second, 32, true};
}

static std::optional<ConstVal> ConstEvalFull(const Expr* expr,
                                             const ScopeMap& scope) {
  if (!expr) return std::nullopt;

  switch (expr->kind) {
    case ExprKind::kIntegerLiteral:
      return ConstEvalLiteral(expr);
    case ExprKind::kStringLiteral:
      return ConstEvalStringLiteral(expr);
    case ExprKind::kIdentifier: {
      // §3.12.1: a $unit:: prefix forces resolution to the compilation-unit
      // scope, bypassing any same-named local that would otherwise shadow it.
      // Those values are aliased under a "$unit::"-qualified key by
      // BuildParamScope, so a match there is the outermost declaration and a
      // miss must not silently fall back to the shadowing local.
      if (expr->scope_prefix == "$unit") {
        std::string key = "$unit::";
        key += expr->text;
        auto uit = scope.find(key);
        if (uit != scope.end()) return ConstVal{uit->second, 32, true};
        return std::nullopt;
      }
      auto it = scope.find(expr->text);
      if (it != scope.end()) return ConstVal{it->second, 32, true};
      return std::nullopt;
    }
    case ExprKind::kUnary:
      return ConstEvalUnaryFull(expr, scope);
    case ExprKind::kBinary:
      return ConstEvalBinaryFull(expr, scope);
    case ExprKind::kTernary: {
      auto cond = ConstEvalFull(expr->condition, scope);
      if (!cond) return std::nullopt;
      return ConstEvalFull(cond->value ? expr->true_expr : expr->false_expr,
                           scope);
    }
    case ExprKind::kConcatenation: {
      auto val = EvalConcat(expr, scope);
      if (!val) return std::nullopt;
      return ConstVal{*val, 32, false};
    }
    case ExprKind::kReplicate: {
      auto val = EvalReplicate(expr, scope);
      if (!val) return std::nullopt;
      return ConstVal{*val, 32, false};
    }
    case ExprKind::kSelect:
      return ConstEvalSelectFull(expr, scope);
    case ExprKind::kSystemCall:
      return ConstEvalSysCallFull(expr, scope);
    case ExprKind::kMemberAccess:
      return ConstEvalMemberAccessFull(expr, scope);
    case ExprKind::kCall:
      // §13.4.3: a call to a user-defined constant function folds at
      // elaboration time.
      return ConstEvalUserCall(expr, scope);
    default:
      return std::nullopt;
  }
}

std::optional<int64_t> ConstEvalInt(const Expr* expr, const ScopeMap& scope) {
  auto result = ConstEvalFull(expr, scope);
  if (!result) return std::nullopt;
  return result->value;
}

std::optional<int64_t> ConstEvalInt(const Expr* expr) {
  static const ScopeMap kEmptyScope;
  return ConstEvalInt(expr, kEmptyScope);
}

static std::optional<double> EvalRealBinary(TokenKind op, double lhs,
                                            double rhs) {
  switch (op) {
    case TokenKind::kPlus:
      return lhs + rhs;
    case TokenKind::kMinus:
      return lhs - rhs;
    case TokenKind::kStar:
      return lhs * rhs;
    case TokenKind::kSlash:
      if (rhs == 0.0) return std::nullopt;
      return lhs / rhs;
    case TokenKind::kPower:
      return std::pow(lhs, rhs);
    default:
      return std::nullopt;
  }
}

static std::optional<double> EvalRealUnary(TokenKind op, double operand) {
  switch (op) {
    case TokenKind::kMinus:
      return -operand;
    case TokenKind::kPlus:
      return operand;
    default:
      return std::nullopt;
  }
}

std::optional<double> ConstEvalReal(const Expr* expr, const ScopeMap& scope) {
  if (!expr) return std::nullopt;

  switch (expr->kind) {
    case ExprKind::kRealLiteral:
    // §5.8: a time literal is interpreted as a realtime (real) value already
    // scaled to the current time unit; the parser folds that scaling into
    // real_val, so in a constant real context it evaluates exactly like any
    // other real literal.
    case ExprKind::kTimeLiteral:
      return expr->real_val;
    case ExprKind::kIntegerLiteral:
      return static_cast<double>(expr->int_val);
    case ExprKind::kIdentifier: {
      auto it = scope.find(expr->text);
      if (it != scope.end()) return static_cast<double>(it->second);
      return std::nullopt;
    }
    case ExprKind::kUnary: {
      auto operand = ConstEvalReal(expr->lhs, scope);
      if (!operand) return std::nullopt;
      return EvalRealUnary(expr->op, *operand);
    }
    case ExprKind::kBinary: {
      auto lhs = ConstEvalReal(expr->lhs, scope);
      auto rhs = ConstEvalReal(expr->rhs, scope);
      if (!lhs || !rhs) return std::nullopt;
      return EvalRealBinary(expr->op, *lhs, *rhs);
    }
    case ExprKind::kTernary: {
      auto cond = ConstEvalInt(expr->condition, scope);
      if (!cond) return std::nullopt;
      return ConstEvalReal(*cond ? expr->true_expr : expr->false_expr, scope);
    }
    case ExprKind::kSystemCall:
    case ExprKind::kCall: {
      // §20.5: the real-returning conversion functions may appear in a constant
      // real context. Each folds from the constant integral value of its arg.
      if (expr->callee == "$itor") {
        if (expr->args.empty()) return std::nullopt;
        auto iv = ConstEvalInt(expr->args[0], scope);
        if (!iv) return std::nullopt;
        return static_cast<double>(*iv);
      }
      if (expr->callee == "$bitstoreal") {
        if (expr->args.empty()) return std::nullopt;
        auto iv = ConstEvalInt(expr->args[0], scope);
        if (!iv) return std::nullopt;
        uint64_t bits = static_cast<uint64_t>(*iv);
        double d = 0.0;
        std::memcpy(&d, &bits, sizeof(d));
        return d;
      }
      if (expr->callee == "$bitstoshortreal") {
        if (expr->args.empty()) return std::nullopt;
        auto iv = ConstEvalInt(expr->args[0], scope);
        if (!iv) return std::nullopt;
        uint32_t bits = static_cast<uint32_t>(*iv);
        float fv = 0.0f;
        std::memcpy(&fv, &bits, sizeof(fv));
        return static_cast<double>(fv);
      }
      return std::nullopt;
    }
    default:
      return std::nullopt;
  }
}

std::optional<double> ConstEvalReal(const Expr* expr) {
  static const ScopeMap kEmptyScope;
  return ConstEvalReal(expr, kEmptyScope);
}

bool IsConstantSysFunc(std::string_view name) {
  static const std::unordered_set<std::string_view> kConstSysFuncs = {
      "$clog2",
      "$bits",
      "$countones",
      "$onehot",
      "$onehot0",
      "$isunknown",
      "$isunbounded",

      "$timescale",
      "$timeprecision",

      "$itor",
      "$rtoi",
      "$bitstoreal",
      "$realtobits",
      "$bitstoshortreal",
      "$shortrealtobits",
      "$signed",
      "$unsigned",

      "$ln",
      "$log10",
      "$exp",
      "$sqrt",
      "$pow",
      "$floor",
      "$ceil",
      "$sin",
      "$cos",
      "$tan",
      "$asin",
      "$acos",
      "$atan",
      "$atan2",
      "$hypot",
      "$sinh",
      "$cosh",
      "$tanh",
      "$asinh",
      "$acosh",
      "$atanh",

      "$dimensions",
      "$unpacked_dimensions",
      "$left",
      "$right",
      "$low",
      "$high",
      "$increment",
      "$size",

      "$countbits",

      "$sformatf",
  };
  return kConstSysFuncs.count(name) > 0;
}

static bool AllElementsConstant(const std::vector<Expr*>& elems,
                                const ScopeMap& scope) {
  for (auto* elem : elems) {
    if (!IsConstantExpr(elem, scope)) return false;
  }
  return true;
}

static bool IsConstEvenWithNonConstArgs(std::string_view name) {
  static const std::unordered_set<std::string_view> kFuncs = {
      "$bits", "$dimensions", "$unpacked_dimensions", "$left", "$right",
      "$low",  "$high",       "$increment",           "$size",
  };
  return kFuncs.count(name) > 0;
}

static bool IsConstantSysCallExpr(const Expr* expr, const ScopeMap& scope) {
  if (!IsConstantSysFunc(expr->callee)) return false;
  if (IsConstEvenWithNonConstArgs(expr->callee)) return true;
  return AllElementsConstant(expr->args, scope);
}

static bool IsTypeOnlyBuiltinMethod(std::string_view method) {
  static const std::unordered_set<std::string_view> kMethods = {
      "size", "num",   "bits", "dimensions", "unpacked_dimensions",
      "left", "right", "low",  "high",       "increment",
  };
  return kMethods.count(method) > 0;
}

static bool IsValueDependentBuiltinMethod(std::string_view method) {
  static const std::unordered_set<std::string_view> kMethods = {
      "len",
  };
  return kMethods.count(method) > 0;
}

static bool IsConstantBuiltinMethodCall(const Expr* expr,
                                        const ScopeMap& scope) {
  if (!expr) return false;
  const Expr* member = nullptr;
  if (expr->kind == ExprKind::kCall && expr->lhs &&
      expr->lhs->kind == ExprKind::kMemberAccess) {
    if (!AllElementsConstant(expr->args, scope)) return false;
    member = expr->lhs;
  } else if (expr->kind == ExprKind::kMemberAccess) {
    member = expr;
  } else {
    return false;
  }
  if (!member->rhs || member->rhs->kind != ExprKind::kIdentifier) return false;
  std::string_view method = member->rhs->text;
  if (IsTypeOnlyBuiltinMethod(method)) return true;
  if (IsValueDependentBuiltinMethod(method)) {
    return IsConstantExpr(member->lhs, scope);
  }
  return false;
}

static bool IsConstantSelectExpr(const Expr* expr, const ScopeMap& scope) {
  if (!IsConstantExpr(expr->base, scope)) return false;
  if (!IsConstantExpr(expr->index, scope)) return false;
  if (expr->index_end && !IsConstantExpr(expr->index_end, scope)) return false;
  return true;
}

static bool IsConstantMemberAccessExpr(const Expr* expr,
                                       const ScopeMap& scope) {
  if (IsConstantBuiltinMethodCall(expr, scope)) return true;
  if (expr->lhs && expr->rhs && expr->lhs->kind == ExprKind::kIdentifier &&
      expr->rhs->kind == ExprKind::kIdentifier) {
    std::string compound =
        std::string(expr->lhs->text) + "." + std::string(expr->rhs->text);
    return scope.count(compound) > 0;
  }
  return false;
}

bool IsConstantExpr(const Expr* expr, const ScopeMap& scope) {
  if (!expr) return false;

  switch (expr->kind) {
    case ExprKind::kIntegerLiteral:
    case ExprKind::kRealLiteral:
    case ExprKind::kStringLiteral:
    case ExprKind::kUnbasedUnsizedLiteral:
    case ExprKind::kTimeLiteral:
      return true;
    case ExprKind::kIdentifier:
      return scope.count(expr->text) > 0;
    case ExprKind::kUnary:
      return IsConstantExpr(expr->lhs, scope);
    case ExprKind::kBinary:
      return IsConstantExpr(expr->lhs, scope) &&
             IsConstantExpr(expr->rhs, scope);
    case ExprKind::kTernary:
      return IsConstantExpr(expr->condition, scope) &&
             IsConstantExpr(expr->true_expr, scope) &&
             IsConstantExpr(expr->false_expr, scope);
    case ExprKind::kConcatenation:
      return AllElementsConstant(expr->elements, scope);
    case ExprKind::kReplicate:
      return IsConstantExpr(expr->repeat_count, scope) &&
             AllElementsConstant(expr->elements, scope);
    case ExprKind::kSelect:
      return IsConstantSelectExpr(expr, scope);
    case ExprKind::kSystemCall:
      return IsConstantSysCallExpr(expr, scope);
    case ExprKind::kCast:
      return IsConstantExpr(expr->lhs, scope);
    case ExprKind::kAssignmentPattern:
      return AllElementsConstant(expr->elements, scope);
    case ExprKind::kCall:
      if (IsConstantBuiltinMethodCall(expr, scope)) return true;
      return AllElementsConstant(expr->args, scope);
    case ExprKind::kMemberAccess:
      return IsConstantMemberAccessExpr(expr, scope);
    default:
      return false;
  }
}

struct StaticPrefixResult {
  std::string text;
  bool is_static;
};

static StaticPrefixResult BuildStaticPrefix(const Expr* expr,
                                            const ScopeMap& scope);

static StaticPrefixResult BuildIdentifierPrefix(const Expr* expr) {
  std::string result;
  if (!expr->scope_prefix.empty()) result += expr->scope_prefix;
  result += expr->text;
  return {result, true};
}

static StaticPrefixResult BuildMemberAccessPrefix(const Expr* expr,
                                                  const ScopeMap& scope) {
  if (!expr->lhs || !expr->rhs) return {"", false};
  auto base = BuildStaticPrefix(expr->lhs, scope);
  if (!base.is_static) return {base.text, false};
  return {base.text + "." + std::string(expr->rhs->text), true};
}

static StaticPrefixResult BuildSelectPrefix(const Expr* expr,
                                            const ScopeMap& scope) {
  auto base = BuildStaticPrefix(expr->base, scope);
  if (base.text.empty()) return {"", false};
  if (!base.is_static) return {base.text, false};
  auto idx = ConstEvalInt(expr->index, scope);
  if (!idx) return {base.text, false};
  return {base.text + "[" + std::to_string(*idx) + "]", true};
}

static StaticPrefixResult BuildStaticPrefix(const Expr* expr,
                                            const ScopeMap& scope) {
  if (!expr) return {"", false};

  if (expr->kind == ExprKind::kIdentifier) {
    return BuildIdentifierPrefix(expr);
  }

  if (expr->kind == ExprKind::kMemberAccess) {
    return BuildMemberAccessPrefix(expr, scope);
  }

  if (expr->kind == ExprKind::kSelect && expr->base) {
    return BuildSelectPrefix(expr, scope);
  }

  return {"", false};
}

std::string LongestStaticPrefix(const Expr* expr, const ScopeMap& scope) {
  if (!expr) return "";
  return BuildStaticPrefix(expr, scope).text;
}

}  // namespace delta
