#include <array>
#include <string_view>
#include <unordered_map>

#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/elaborator_validate_operations.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// §11.3.1: the operators whose result is real when an
// operand is, the arithmetic ones. A relational, an equality or a logical
// operator gives a one-bit result whatever its operands.
constexpr std::array<TokenKind, 5> kRealPropagatingOps = {
    TokenKind::kPlus, TokenKind::kMinus, TokenKind::kStar, TokenKind::kSlash,
    TokenKind::kPower};

}  // namespace

static bool PropagatesReal(TokenKind op) {
  for (TokenKind arithmetic : kRealPropagatingOps) {
    if (op == arithmetic) return true;
  }
  return false;
}

static DataTypeKind VarKind(
    const Expr* e,
    const std::unordered_map<std::string_view, DataTypeKind>& var_types) {
  auto it = var_types.find(e->text);
  return it == var_types.end() ? DataTypeKind::kImplicit : it->second;
}

bool IsRealValued(
    const Expr* e,
    const std::unordered_map<std::string_view, DataTypeKind>& var_types) {
  if (e->kind == ExprKind::kRealLiteral || e->kind == ExprKind::kTimeLiteral) {
    return true;
  }
  if (e->kind == ExprKind::kIdentifier) {
    return IsRealType(VarKind(e, var_types));
  }
  // An element of an array of reals (§7.4) is a real; var_types records the
  // array under its element's kind.
  if (e->kind == ExprKind::kSelect) {
    auto it = var_types.find(ExprIdent(e->base));
    return it != var_types.end() && IsRealType(it->second);
  }
  if (e->kind == ExprKind::kUnary || e->kind == ExprKind::kBinary) {
    return PropagatesReal(e->op) &&
           (IsRealValued(e->lhs, var_types) ||
            (e->rhs != nullptr && IsRealValued(e->rhs, var_types)));
  }
  if (e->kind == ExprKind::kTernary) {
    return IsRealValued(e->true_expr, var_types) ||
           IsRealValued(e->false_expr, var_types);
  }
  return false;
}

// §6.24.1 (printed page 140) requires the operand of a size or a signing cast
// to be integral (§6.11.1). A real value is not, nor is a variable of a string,
// chandle or event type, a class handle, an unpacked array or a variable of an
// unpacked structure or union type.
bool ElaboratorOperationRules::CastOperandIsNonIntegral(
    const Expr* operand) const {
  if (IsRealValued(operand, var_types_)) return true;
  if (operand->kind != ExprKind::kIdentifier) return false;
  DataTypeKind kind = VarKind(operand, var_types_);
  if (kind == DataTypeKind::kString || kind == DataTypeKind::kChandle ||
      kind == DataTypeKind::kEvent) {
    return true;
  }
  if (class_var_names_.count(operand->text) != 0 ||
      cast_unpacked_structs_.count(operand->text) != 0) {
    return true;
  }
  // var_array_info_ records a variable only when it is declared with an
  // unpacked dimension.
  return var_array_info_.count(operand->text) != 0;
}

}  // namespace delta
