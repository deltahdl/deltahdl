#include "common/arena.h"
#include "common/diagnostic.h"
#include "lexer/lexer.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "parser/parser.h"
#include "parser/parser_data_decl_internal.h"

namespace delta {

static bool IsAssocIndexType(TokenKind tk) {
  return TokenToTypeKind(tk).has_value() && tk != TokenKind::kKwVoid;
}

static bool TakesSigning(TokenKind tk) {
  DataTypeKind kind = TokenToTypeKind(tk).value_or(DataTypeKind::kImplicit);
  return ParserDataDeclHelpers::IsIntegerAtomKind(kind) ||
         ParserDataDeclHelpers::IsIntegerVectorKind(kind);
}

bool ParserDataDeclHelpers::AtIndexType(Parser& p) {
  TokenKind kind = p.CurrentToken().kind;
  if (IsAssocIndexType(kind) || kind == TokenKind::kKwEnum ||
      kind == TokenKind::kKwStruct || kind == TokenKind::kKwUnion) {
    return true;
  }
  if (kind != TokenKind::kIdentifier) return false;
  auto saved = p.lexer_.SavePos();
  p.Consume();
  bool parameterized = p.Check(TokenKind::kHash);
  p.lexer_.RestorePos(saved);
  return parameterized;
}

DataType ParserDataDeclHelpers::ReadIndexDataType(Parser& p) {
  if (p.Check(TokenKind::kKwEnum)) return p.ParseEnumType();
  if (p.Check(TokenKind::kKwStruct) || p.Check(TokenKind::kKwUnion)) {
    DataType type = p.ParseStructOrUnionType();
    p.ParsePackedDims(type);
    return type;
  }
  return p.ParseDataType();
}

Expr* Parser::ParseAssocIndexDim() {
  if (!IsAssocIndexType(CurrentToken().kind)) {
    auto* ref = arena_.Create<Expr>();
    ref->kind = ExprKind::kTypeRef;
    ref->range.start = CurrentLoc();
    ref->type_value = arena_.Create<DataType>(
        ParserDataDeclHelpers::ReadIndexDataType(*this));
    ref->text = ref->type_value->type_name;
    return ref;
  }
  if (IsNetTypeToken(CurrentToken().kind)) {
    diag_.Error(CurrentLoc(),
                "a net type is no data type and cannot index an associative "
                "array",
                Subclause("A.2.5"));
  }
  auto* dim = arena_.Create<Expr>();
  dim->kind = ExprKind::kIdentifier;
  bool takes_signing = TakesSigning(CurrentToken().kind);
  Token type_tok = Consume();
  dim->range.start = type_tok.loc;
  dim->text = type_tok.text;
  if (takes_signing &&
      (Check(TokenKind::kKwSigned) || Check(TokenKind::kKwUnsigned))) {
    dim->op = Consume().kind;
  }
  while (Check(TokenKind::kLBracket)) {
    Consume();
    auto* packed = arena_.Create<Expr>();
    packed->kind = ExprKind::kBinary;
    packed->op = TokenKind::kColon;
    packed->lhs = ParseExpr();
    Expect(TokenKind::kColon, Subclause("7.4.1"));
    packed->rhs = ParseExpr();
    Expect(TokenKind::kRBracket, Subclause("7.4.1"));
    packed->range.start = packed->lhs->range.start;
    dim->elements.push_back(packed);
  }
  return dim;
}

}  // namespace delta
