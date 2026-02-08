#include "elaboration/const_eval.h"

#include "lexer/token.h"
#include "parser/ast.h"

namespace delta {

// Evaluate a binary arithmetic operation on two constant integers.
static std::optional<int64_t> eval_binary(TokenKind op, int64_t lhs, int64_t rhs) {
    switch (op) {
    case TokenKind::Plus:    return lhs + rhs;
    case TokenKind::Minus:   return lhs - rhs;
    case TokenKind::Star:    return lhs * rhs;
    case TokenKind::Slash:
        if (rhs == 0) return std::nullopt;
        return lhs / rhs;
    case TokenKind::Percent:
        if (rhs == 0) return std::nullopt;
        return lhs % rhs;
    default:
        return std::nullopt;
    }
}

// Evaluate a unary operation on a constant integer.
static std::optional<int64_t> eval_unary(TokenKind op, int64_t operand) {
    switch (op) {
    case TokenKind::Minus: return -operand;
    case TokenKind::Plus:  return operand;
    case TokenKind::Tilde: return ~operand;
    case TokenKind::Bang:  return operand == 0 ? 1 : 0;
    default:
        return std::nullopt;
    }
}

std::optional<int64_t> const_eval_int(const Expr* expr) {
    if (!expr) return std::nullopt;

    switch (expr->kind) {
    case ExprKind::IntegerLiteral:
        return static_cast<int64_t>(expr->int_val);

    case ExprKind::Unary: {
        auto operand = const_eval_int(expr->lhs);
        if (!operand) return std::nullopt;
        return eval_unary(expr->op, *operand);
    }

    case ExprKind::Binary: {
        auto lhs = const_eval_int(expr->lhs);
        auto rhs = const_eval_int(expr->rhs);
        if (!lhs || !rhs) return std::nullopt;
        return eval_binary(expr->op, *lhs, *rhs);
    }

    default:
        return std::nullopt;
    }
}

} // namespace delta
