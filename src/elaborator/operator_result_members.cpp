#include "elaborator/operator_result_members.h"

#include <format>

#include "common/diagnostic.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"

namespace delta {

// §11.8.1: whether `e` is an operator's expression, whose result is an
// integral or a real value: a unary operator's, an increment's or a
// decrement's, `inside`'s (§11.4.13), and a binary operator's other than `=`.
static bool YieldsIntegralOrReal(const Expr& e) {
  switch (e.kind) {
    case ExprKind::kUnary:
    case ExprKind::kPostfixUnary:
    case ExprKind::kInside:
      return true;
    case ExprKind::kBinary:
      return e.op != TokenKind::kEq;
    default:
      return false;
  }
}

void ReportOperatorResultMember(const Expr& access, DiagEngine& diag) {
  if (!YieldsIntegralOrReal(*access.lhs)) return;
  diag.Error(access.rhs->range.start,
             std::format("'{}' is no member or built-in method of the integral "
                         "or real value an operator yields",
                         access.rhs->text),
             Subclause("11.8.1"));
}

}  // namespace delta
