#include "simulator/sequence_actual_cast.h"

#include <string_view>

#include "common/arena.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/expr_substitute.h"
#include "simulator/evaluation_internal.h"

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

// §16.8: an actual bound to an untyped formal is enclosed in parentheses and
// cast to its self-determined type before it stands for the formal, here a
// size cast to its own $bits, which §6.24.1 has keep its signedness. Only an
// operator's result takes a width from its context (§11.6.1), so a name, a
// select, a call, a concatenation and a literal, `$` and every
// variable_lvalue among them, stand as written, as do a sequence or property
// actual, an event actual and a real.
Expr* SelfDeterminedActual(Expr* actual, SimContext& ctx, Arena& arena) {
  bool is_operator = actual->kind == ExprKind::kBinary ||
                     actual->kind == ExprKind::kUnary ||
                     actual->kind == ExprKind::kTernary;
  if (!is_operator || actual->property_actual != nullptr ||
      IsEventActual(actual) || SimSelfReal(actual, ctx)) {
    return actual;
  }
  auto* bits = arena.Create<Expr>();
  bits->kind = ExprKind::kSystemCall;
  bits->callee = "$bits";
  bits->range = actual->range;
  bits->args.push_back(actual);
  auto* cast = arena.Create<Expr>();
  cast->kind = ExprKind::kCast;
  cast->range = actual->range;
  cast->lhs = actual;
  cast->rhs = bits;
  return cast;
}

}  // namespace

Expr* CastActualToFormal(Expr* actual, TokenKind type_kw, SimContext& ctx,
                         Arena& arena) {
  if (actual == nullptr) return actual;
  return type_kw == TokenKind::kKwUntyped
             ? SelfDeterminedActual(actual, ctx, arena)
             : CastToKeywordType(actual, type_kw, arena);
}

}  // namespace delta
