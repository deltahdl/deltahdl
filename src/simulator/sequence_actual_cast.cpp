#include "simulator/sequence_actual_cast.h"

#include <string_view>

#include "common/arena.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/expr_substitute.h"

namespace delta {

namespace {

// §16.8.1 (c): an actual bound to a formal of a keyword data type is cast to
// that type before it is substituted, so an 8-bit actual passed to a `bit`
// formal is truncated and a `bit` passed to a `byte` formal extended. A `$`
// and an event actual are substituted as they are.
Expr* CastToKeywordType(Expr* actual, TokenKind type_kw, Arena& arena) {
  if (type_kw == TokenKind::kEof) return actual;
  if (IsEventActual(actual)) return actual;
  if (actual->kind == ExprKind::kIdentifier && actual->text == "$") {
    return actual;
  }
  std::string_view type_name;
  switch (type_kw) {
    case TokenKind::kKwBit:
      type_name = "bit";
      break;
    case TokenKind::kKwLogic:
      type_name = "logic";
      break;
    case TokenKind::kKwReg:
      type_name = "reg";
      break;
    case TokenKind::kKwByte:
      type_name = "byte";
      break;
    case TokenKind::kKwShortint:
      type_name = "shortint";
      break;
    case TokenKind::kKwInt:
      type_name = "int";
      break;
    case TokenKind::kKwLongint:
      type_name = "longint";
      break;
    case TokenKind::kKwInteger:
      type_name = "integer";
      break;
    default:
      return actual;
  }
  auto* cast = arena.Create<Expr>();
  cast->kind = ExprKind::kCast;
  cast->text = type_name;
  cast->range = actual->range;
  cast->lhs = actual;
  return cast;
}

}  // namespace

Expr* CastActualToFormal(Expr* actual, TokenKind type_kw, Arena& arena) {
  if (actual == nullptr) return actual;
  return CastToKeywordType(actual, type_kw, arena);
}

}  // namespace delta
