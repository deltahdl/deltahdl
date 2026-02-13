#include "elaboration/const_eval.h"

#include "lexer/token.h"
#include "parser/ast.h"

namespace delta {

// Evaluate a constant power expression.
static std::optional<int64_t> EvalPower(int64_t base, int64_t exp) {
  if (exp < 0) return std::nullopt;
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
      return lhs + rhs;
    case TokenKind::kMinus:
      return lhs - rhs;
    case TokenKind::kStar:
      return lhs * rhs;
    case TokenKind::kSlash:
      if (rhs == 0) return std::nullopt;
      return lhs / rhs;
    case TokenKind::kPercent:
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
      return lhs & rhs;
    case TokenKind::kPipe:
      return lhs | rhs;
    case TokenKind::kCaret:
      return lhs ^ rhs;
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
      return ~(lhs ^ rhs);
    case TokenKind::kLtLt:
    case TokenKind::kLtLtLt:
      return lhs << rhs;
    case TokenKind::kGtGt:
      return static_cast<int64_t>(static_cast<uint64_t>(lhs) >> rhs);
    case TokenKind::kGtGtGt:
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

// Constant-evaluate a system call ($clog2).
static std::optional<int64_t> EvalConstSysCall(const Expr* expr,
                                               const ScopeMap& scope) {
  if (expr->callee == "$clog2" && !expr->args.empty()) {
    auto arg = ConstEvalInt(expr->args[0], scope);
    if (!arg) return std::nullopt;
    return Clog2(*arg);
  }
  return std::nullopt;
}

std::optional<int64_t> ConstEvalInt(const Expr* expr, const ScopeMap& scope) {
  if (!expr) return std::nullopt;

  switch (expr->kind) {
    case ExprKind::kIntegerLiteral:
      return static_cast<int64_t>(expr->int_val);
    case ExprKind::kIdentifier: {
      auto it = scope.find(expr->text);
      if (it != scope.end()) return it->second;
      return std::nullopt;
    }
    case ExprKind::kUnary: {
      auto operand = ConstEvalInt(expr->lhs, scope);
      if (!operand) return std::nullopt;
      return EvalUnary(expr->op, *operand);
    }
    case ExprKind::kBinary: {
      auto lhs = ConstEvalInt(expr->lhs, scope);
      auto rhs = ConstEvalInt(expr->rhs, scope);
      if (!lhs || !rhs) return std::nullopt;
      return EvalBinary(expr->op, *lhs, *rhs);
    }
    case ExprKind::kTernary: {
      auto cond = ConstEvalInt(expr->condition, scope);
      if (!cond) return std::nullopt;
      return ConstEvalInt(*cond ? expr->true_expr : expr->false_expr, scope);
    }
    case ExprKind::kConcatenation:
      return EvalConcat(expr, scope);
    case ExprKind::kReplicate:
      return EvalReplicate(expr, scope);
    case ExprKind::kSystemCall:
      return EvalConstSysCall(expr, scope);
    default:
      return std::nullopt;
  }
}

std::optional<int64_t> ConstEvalInt(const Expr* expr) {
  static const ScopeMap kEmptyScope;
  return ConstEvalInt(expr, kEmptyScope);
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
