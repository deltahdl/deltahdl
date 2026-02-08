#include "elaboration/const_eval.h"

#include "lexer/token.h"
#include "parser/ast.h"

namespace delta {

// Evaluate a binary arithmetic operation on two constant integers.
static std::optional<int64_t> EvalBinary(TokenKind op, int64_t lhs,
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
    default:
      return std::nullopt;
  }
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

std::optional<int64_t> ConstEvalInt(const Expr* expr) {
  if (!expr) return std::nullopt;

  switch (expr->kind) {
    case ExprKind::kIntegerLiteral:
      return static_cast<int64_t>(expr->int_val);

    case ExprKind::kUnary: {
      auto operand = ConstEvalInt(expr->lhs);
      if (!operand) return std::nullopt;
      return EvalUnary(expr->op, *operand);
    }

    case ExprKind::kBinary: {
      auto lhs = ConstEvalInt(expr->lhs);
      auto rhs = ConstEvalInt(expr->rhs);
      if (!lhs || !rhs) return std::nullopt;
      return EvalBinary(expr->op, *lhs, *rhs);
    }

    default:
      return std::nullopt;
  }
}

}  // namespace delta
