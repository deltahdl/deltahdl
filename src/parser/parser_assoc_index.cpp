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

// A.2.2.1 attaches an optional signing to the integer types alone:
// `integer_vector_type [ signing ] { packed_dimension }` and
// `integer_atom_type [ signing ]`. No other data_type production admits one.
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

// Parses the type naming an associative array's index, positioned where
// AtIndexType found it opening. §7.8 makes an index_type a data_type, so a
// data_type built on an integer type carries the optional signing that A.2.2.1
// gives it and `[byte unsigned]` is a legal index type. The qualifier is held
// in `op` because it decides how the keys order: an unsigned byte index sorts
// key 200 above key 50, while a signed one reads that key as -56 and sorts it
// below. A.2.2.1 writes `integer_vector_type [ signing ] { packed_dimension }`,
// so the packed dimensions after the signing are part of the same data_type
// and `[bit [3:0]]` is a legal index type too. They are kept because §7.8.4
// keys an entry off the index cast to the declared index width: `bit [3:0]`
// holds sixteen entries and reads index 17 as 1, while a bare `bit` holds two,
// so the two declarations are different arrays. Each one is appended to
// `elements` in declaration order as a `[msb:lsb]` range.
Expr* Parser::ParseAssocIndexDim() {
  // A.2.5 writes the index as a data_type, and one an expression cannot spell
  // is kept as the type reference `type(data_type)` makes, its type in
  // type_value (§6.23), the elaborator reading the two alike.
  if (!IsAssocIndexType(CurrentToken().kind)) {
    auto* ref = arena_.Create<Expr>();
    ref->kind = ExprKind::kTypeRef;
    ref->range.start = CurrentLoc();
    ref->type_value = arena_.Create<DataType>(
        ParserDataDeclHelpers::ReadIndexDataType(*this));
    ref->text = ref->type_value->type_name;
    return ref;
  }
  // A.2.5 reads the index as a data_type, which A.2.2.1's net_type is no form
  // of, so a net type keyword is reported here and the dimension read on.
  if (IsNetTypeToken(CurrentToken().kind)) {
    diag_.Error(CurrentLoc(),
                "a net type is no data type and cannot index an associative "
                "array",
                Subclause("A.2.5"));
  }
  auto* dim = arena_.Create<Expr>();
  dim->kind = ExprKind::kIdentifier;
  bool takes_signing = TakesSigning(CurrentToken().kind);
  // §7.8 writes the index type as the keyword itself, so the dimension begins
  // at that keyword.
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
    // §7.4.1 states the rule both these calls enforce: every packed dimension
    // of a packed array declaration takes a range specification [
    // constant_expression : constant_expression ].
    Expect(TokenKind::kColon, Subclause("7.4.1"));
    packed->rhs = ParseExpr();
    Expect(TokenKind::kRBracket, Subclause("7.4.1"));
    // The dimension begins where its first bound begins, as §7.4.2 writes the
    // dimension as that bound followed by the colon.
    packed->range.start = packed->lhs->range.start;
    dim->elements.push_back(packed);
  }
  return dim;
}

}  // namespace delta
