#include "simulator/sequence_actual_cast.h"

#include <string_view>

#include "common/arena.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "parser/expr_substitute.h"

namespace delta {

namespace {

bool StandsAsWritten(const Expr* actual) {
  return IsEventActual(actual) ||
         (actual->kind == ExprKind::kIdentifier && actual->text == "$");
}

Expr* CastOf(Expr* actual, Arena& arena) {
  auto* cast = arena.Create<Expr>();
  cast->kind = ExprKind::kCast;
  cast->range = actual->range;
  cast->lhs = actual;
  return cast;
}

Expr* NameOf(std::string_view name, const Expr* at, Arena& arena) {
  auto* id = arena.Create<Expr>();
  id->kind = ExprKind::kIdentifier;
  id->range = at->range;
  id->text = name;
  return id;
}

Expr* CastToKeywordType(Expr* actual, TokenKind type_kw, const DataType* type,
                        Arena& arena) {
  std::string_view type_name;
  bool signed_by_default = true;
  switch (type_kw) {
    case TokenKind::kKwBit:
      type_name = "bit";
      signed_by_default = false;
      break;
    case TokenKind::kKwLogic:
      type_name = "logic";
      signed_by_default = false;
      break;
    case TokenKind::kKwReg:
      type_name = "reg";
      signed_by_default = false;
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
  Expr* cast = CastOf(actual, arena);
  cast->text = type_name;
  if (type->is_signed == signed_by_default) return cast;
  Expr* signing = CastOf(cast, arena);
  signing->text = type->is_signed ? "signed" : "unsigned";
  return signing;
}

Expr* CastToDataType(Expr* actual, DataType* type, Arena& arena) {
  Expr* cast = CastOf(actual, arena);
  if (type->kind != DataTypeKind::kNamed || type->packed_dim_left != nullptr) {
    auto* ref = arena.Create<Expr>();
    ref->kind = ExprKind::kTypeRef;
    ref->range = actual->range;
    ref->type_value = type;
    cast->rhs = ref;
  } else if (type->scope_name.empty()) {
    cast->text = type->type_name;
  } else {
    auto* scoped = arena.Create<Expr>();
    scoped->kind = ExprKind::kMemberAccess;
    scoped->range = actual->range;
    scoped->is_scope_resolution = true;
    scoped->lhs = NameOf(type->scope_name, actual, arena);
    scoped->rhs = NameOf(type->type_name, actual, arena);
    cast->rhs = scoped;
  }
  return cast;
}

}  // namespace

Expr* CastActualToFormal(Expr* actual, TokenKind type_kw, DataType* type,
                         Arena& arena) {
  if (actual == nullptr) return actual;
  if (type_kw == TokenKind::kKwUntyped) {
    return SelfDeterminedActual(actual, arena);
  }
  if (StandsAsWritten(actual)) return actual;
  if (type_kw != TokenKind::kEof) {
    return CastToKeywordType(actual, type_kw, type, arena);
  }
  return CastToDataType(actual, type, arena);
}

}  // namespace delta
