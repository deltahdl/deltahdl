#include "elaborator/const_eval.h"

#include <cmath>
#include <unordered_set>

#include "lexer/token.h"
#include "parser/ast.h"

namespace delta {

// Evaluate a constant power expression.
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

// Evaluate a binary operation on two constant integers.
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

// Evaluate a binary bitwise or shift operation.
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

// Evaluate a binary comparison or logical operation.
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

// Evaluate a binary operation on two constant integers.
static std::optional<int64_t> EvalBinary(TokenKind op, int64_t lhs,
                                         int64_t rhs) {
  auto result = EvalBinaryArith(op, lhs, rhs);
  if (result) return result;
  result = EvalBinaryBitwise(op, lhs, rhs);
  if (result) return result;
  return EvalBinaryCompare(op, lhs, rhs);
}

// Evaluate a unary operation on a constant integer.
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

// Width of a literal from its text (e.g., "4'd3" → 4, "8'hFF" → 8).
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

// §20.4.1: $clog2 — ceiling of log base 2.
static int64_t Clog2(int64_t val) {
  if (val <= 1) return 0;
  int64_t result = 0;
  int64_t v = val - 1;
  while (v > 0) {
    v >>= 1;
    ++result;
  }
  return result;
}

// Constant-evaluate a concatenation: {a, b, c}.
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

// Constant-evaluate a replication: {n{expr}}.
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

// §20.9.2: $countones — count number of 1-bits.
static int64_t Countones(int64_t val) {
  auto u = static_cast<uint64_t>(val);
  int64_t count = 0;
  while (u != 0) {
    u &= u - 1;
    ++count;
  }
  return count;
}

// Evaluate the first argument of a constant system call.
static std::optional<int64_t> EvalFirstArg(const Expr* expr,
                                           const ScopeMap& scope) {
  if (expr->args.empty()) return std::nullopt;
  return ConstEvalInt(expr->args[0], scope);
}

// §20.6.2: Evaluate $bits in a constant context.
static std::optional<int64_t> EvalConstBits(const Expr* expr) {
  if (expr->args.empty()) return std::nullopt;
  auto* a = expr->args[0];
  if (a->kind == ExprKind::kIntegerLiteral)
    return static_cast<int64_t>(ConstLiteralWidth(a));
  return std::nullopt;
}

// Constant-evaluate a system call ($clog2, $bits, $countones, etc.).
static std::optional<int64_t> EvalConstSysCall(const Expr* expr,
                                               const ScopeMap& scope) {
  if (expr->callee == "$bits") return EvalConstBits(expr);
  auto arg = EvalFirstArg(expr, scope);
  if (!arg) return std::nullopt;
  if (expr->callee == "$clog2") return Clog2(*arg);
  if (expr->callee == "$countones") return Countones(*arg);
  if (expr->callee == "$onehot")
    return static_cast<int64_t>(Countones(*arg) == 1);
  if (expr->callee == "$onehot0")
    return static_cast<int64_t>(Countones(*arg) <= 1);
  return std::nullopt;
}

// §11.3.3: Internal representation for constant evaluation with signedness.
struct ConstVal {
  int64_t value;
  uint32_t width;
  bool is_signed;
};

// §11.3.3: Determine signedness of a literal from its text.
static bool IsSignedLiteral(std::string_view text) {
  auto tick = text.find('\'');
  if (tick == std::string_view::npos) return true;
  if (tick + 1 >= text.size()) return false;
  char c = text[tick + 1];
  return c == 's' || c == 'S';
}

// Truncate a value to the given bit width.
static int64_t TruncateToWidth(int64_t val, uint32_t width) {
  if (width == 0 || width >= 64) return val;
  return static_cast<int64_t>(static_cast<uint64_t>(val) &
                               ((uint64_t{1} << width) - 1));
}

// Sign-extend a truncated value from the given bit width to 64 bits.
static int64_t SignExtendFromWidth(int64_t val, uint32_t width) {
  if (width == 0 || width >= 64) return val;
  uint64_t mask = (uint64_t{1} << width) - 1;
  uint64_t uval = static_cast<uint64_t>(val) & mask;
  if (uval & (uint64_t{1} << (width - 1))) {
    uval |= ~mask;
  }
  return static_cast<int64_t>(uval);
}

// Constant-evaluate an expression, tracking signedness and width per §11.3.3.
static std::optional<ConstVal> ConstEvalFull(const Expr* expr,
                                             const ScopeMap& scope) {
  if (!expr) return std::nullopt;

  switch (expr->kind) {
    case ExprKind::kIntegerLiteral: {
      uint32_t w = ConstLiteralWidth(expr);
      bool s = IsSignedLiteral(expr->text);
      int64_t v = TruncateToWidth(static_cast<int64_t>(expr->int_val), w);
      if (s) v = SignExtendFromWidth(v, w);
      return ConstVal{v, w, s};
    }
    case ExprKind::kIdentifier: {
      auto it = scope.find(expr->text);
      if (it != scope.end()) return ConstVal{it->second, 32, true};
      return std::nullopt;
    }
    case ExprKind::kUnary: {
      auto operand = ConstEvalFull(expr->lhs, scope);
      if (!operand) return std::nullopt;
      if (expr->op == TokenKind::kMinus) {
        int64_t v = TruncateToWidth(-operand->value, operand->width);
        if (operand->is_signed) v = SignExtendFromWidth(v, operand->width);
        return ConstVal{v, operand->width, operand->is_signed};
      }
      auto result = EvalUnary(expr->op, operand->value);
      if (!result) return std::nullopt;
      return ConstVal{*result, operand->width, operand->is_signed};
    }
    case ExprKind::kBinary: {
      auto lhs = ConstEvalFull(expr->lhs, scope);
      auto rhs = ConstEvalFull(expr->rhs, scope);
      if (!lhs || !rhs) return std::nullopt;
      uint32_t w = std::max(lhs->width, rhs->width);
      bool s = lhs->is_signed && rhs->is_signed;
      int64_t lv, rv;
      if (s) {
        lv = SignExtendFromWidth(lhs->value, lhs->width);
        rv = SignExtendFromWidth(rhs->value, rhs->width);
      } else {
        lv = TruncateToWidth(lhs->value, lhs->width);
        rv = TruncateToWidth(rhs->value, rhs->width);
      }
      if (!s && (expr->op == TokenKind::kSlash ||
                 expr->op == TokenKind::kSlashEq)) {
        auto ul = static_cast<uint64_t>(lv);
        auto ur = static_cast<uint64_t>(rv);
        if (ur == 0) return std::nullopt;
        return ConstVal{static_cast<int64_t>(ul / ur), w, false};
      }
      if (!s && (expr->op == TokenKind::kPercent ||
                 expr->op == TokenKind::kPercentEq)) {
        auto ul = static_cast<uint64_t>(lv);
        auto ur = static_cast<uint64_t>(rv);
        if (ur == 0) return std::nullopt;
        return ConstVal{static_cast<int64_t>(ul % ur), w, false};
      }
      auto result = EvalBinary(expr->op, lv, rv);
      if (!result) return std::nullopt;
      return ConstVal{*result, w, s};
    }
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
    case ExprKind::kSelect: {
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
    case ExprKind::kSystemCall: {
      auto val = EvalConstSysCall(expr, scope);
      if (!val) return std::nullopt;
      return ConstVal{*val, 32, true};
    }
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

// --- §11.2.1: Constant real evaluation ---

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
    default:
      return std::nullopt;
  }
}

std::optional<double> ConstEvalReal(const Expr* expr) {
  static const ScopeMap kEmptyScope;
  return ConstEvalReal(expr, kEmptyScope);
}

// --- §11.2.1: Constant expression predicate ---

// System functions that are constant when their arguments are constant.
static bool IsConstantSysFunc(std::string_view name) {
  static const std::unordered_set<std::string_view> kConstSysFuncs = {
      "$clog2",
      "$bits",
      "$countones",
      "$onehot",
      "$onehot0",
      "$isunbounded",
      // §20.4: Timescale system functions
      "$timescale",
      "$timeprecision",
      // §20.5: Conversion functions
      "$itor",
      "$rtoi",
      "$bitstoreal",
      "$realtobits",
      "$bitstoshortreal",
      "$shortrealtobits",
      "$signed",
      "$unsigned",
      // §20.8: Math functions
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
      // §20.7: Array query functions
      "$dimensions",
      "$unpacked_dimensions",
      "$left",
      "$right",
      "$low",
      "$high",
      "$increment",
      "$size",
      // §20.9: Bit vector system functions
      "$countbits",
      // §21.3.3
      "$sformatf",
  };
  return kConstSysFuncs.count(name) > 0;
}

// Check that all elements in a vector are constant expressions.
static bool AllElementsConstant(const std::vector<Expr*>& elems,
                                const ScopeMap& scope) {
  for (auto* elem : elems) {
    if (!IsConstantExpr(elem, scope)) return false;
  }
  return true;
}

// §11.2.1: Data query (§20.6) and array query (§20.7) system functions may be
// constant even when their arguments are not constant.
static bool IsConstEvenWithNonConstArgs(std::string_view name) {
  static const std::unordered_set<std::string_view> kFuncs = {
      "$bits",   "$dimensions", "$unpacked_dimensions", "$left",
      "$right",  "$low",        "$high",                "$increment",
      "$size",
  };
  return kFuncs.count(name) > 0;
}

// Check that a system call with constant arguments is a constant expression.
static bool IsConstantSysCallExpr(const Expr* expr, const ScopeMap& scope) {
  if (!IsConstantSysFunc(expr->callee)) return false;
  if (IsConstEvenWithNonConstArgs(expr->callee)) return true;
  return AllElementsConstant(expr->args, scope);
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
      if (!IsConstantExpr(expr->base, scope)) return false;
      if (!IsConstantExpr(expr->index, scope)) return false;
      if (expr->index_end && !IsConstantExpr(expr->index_end, scope))
        return false;
      return true;
    case ExprKind::kSystemCall:
      return IsConstantSysCallExpr(expr, scope);
    case ExprKind::kCast:
      return IsConstantExpr(expr->lhs, scope);
    default:
      return false;
  }
}

// §11.5.3: Build the textual representation of a static prefix.
static std::string BuildStaticPrefix(const Expr* expr, const ScopeMap& scope) {
  if (!expr) return "";
  if (expr->kind == ExprKind::kIdentifier) return std::string(expr->text);
  if (expr->kind != ExprKind::kSelect || !expr->base) return "";
  std::string base = BuildStaticPrefix(expr->base, scope);
  if (base.empty()) return "";
  // Check if index is a constant expression.
  auto idx = ConstEvalInt(expr->index, scope);
  if (!idx) return base;  // Non-constant index → stop here.
  return base + "[" + std::to_string(*idx) + "]";
}

std::string LongestStaticPrefix(const Expr* expr, const ScopeMap& scope) {
  if (!expr) return "";
  // For a select chain, walk recursively.
  if (expr->kind == ExprKind::kSelect) return BuildStaticPrefix(expr, scope);
  // For a plain identifier, the prefix is the identifier itself.
  if (expr->kind == ExprKind::kIdentifier) return std::string(expr->text);
  return "";
}

}  // namespace delta
