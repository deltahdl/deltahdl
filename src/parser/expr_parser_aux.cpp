#include "common/diagnostic.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "parser/parser.h"
#include "parser/parser_token_skips.h"

namespace delta {

// Answers whether the token standing after `new` opens a shallow-copy source.
// A.2.4 gives class_new the two alternatives
// `[ class_scope ] new [ ( list_of_arguments ) ]` and `new expression`, and
// footnote 23 on that production requires the second's expression to "evaluate
// to an object handle". Two tokens can open one. An identifier can name a
// handle variable, and `this` is one outright: §8.11 says "The this keyword
// denotes a predefined object handle that refers to the object that was used to
// invoke the subroutine that this is used within".
//
// No third token is admitted, because the two that remain belong to the other
// productions. A '(' after `new` is the first alternative's list_of_arguments,
// which is what distinguishes the two alternatives at all. A '[' is
// dynamic_array_new, `new [ expression ] [ ( expression ) ]` in A.2.4, and
// Parser::ParseNewExpr reads it before asking this.
//
// Parser::ParseNewExpr and Parser::MakeMemberAccess both ask, and have to
// agree: the first decides what `new` takes as a copy source, and the second
// reports §8.12's "It shall be illegal to use a typed constructor call for a
// shallow copy" over the same source when a class scope precedes the `new`. A
// source one admits and the other does not is either accepted with the class
// scope or left standing where a statement terminator belongs.
bool Parser::StartsShallowCopySource() {
  return CheckIdentifier() || Check(TokenKind::kKwThis);
}

Expr* Parser::ParseStreamingConcat(TokenKind dir) {
  auto loc = CurrentLoc();
  Consume();
  auto* sc = arena_.Create<Expr>();
  sc->kind = ExprKind::kStreamingConcat;
  sc->range.start = loc;
  sc->op = dir;

  if (!Check(TokenKind::kLBrace)) {
    auto saved = lexer_.SavePos();
    auto tok = Consume();
    if (Check(TokenKind::kLBrace)) {
      auto* type_id = arena_.Create<Expr>();
      type_id->kind = ExprKind::kIdentifier;
      type_id->text = tok.text;
      type_id->range.start = tok.loc;
      sc->lhs = type_id;
    } else {
      lexer_.RestorePos(saved);
      sc->lhs = ParsePrimaryExpr();
    }
  }

  Expect(TokenKind::kLBrace, Subclause("11.4.14"));
  sc->elements.push_back(ParseExpr());
  while (Match(TokenKind::kComma)) {
    sc->elements.push_back(ParseExpr());
  }
  Expect(TokenKind::kRBrace, Subclause("11.4.14"));
  return sc;
}

// A.8.2's `( list_of_arguments )` of a subroutine call or a class_new: the
// list is ordered and then named, or named from its first element, and either
// may be empty. Each argument lands in call->args, and a named one records its
// name in call->arg_names as well.
void Parser::ParseListOfArguments(Expr* call) {
  Expect(TokenKind::kLParen, Subclause("13.5"));
  if (!Check(TokenKind::kRParen)) {
    if (Check(TokenKind::kDot)) {
      ParseTrailingNamedArgs(call);
    } else {
      ParseCallArgs(call);
    }
  }
  Expect(TokenKind::kRParen, Subclause("13.5"));
}

void Parser::ParseNamedArg(Expr* call) {
  Expect(TokenKind::kDot, Subclause("13.5.4"));
  auto name_tok = Expect(TokenKind::kIdentifier, Subclause("13.5.4"));
  Expect(TokenKind::kLParen, Subclause("13.5.4"));
  Expr* value = nullptr;
  if (!Check(TokenKind::kRParen)) {
    value = ParseExpr();
  }
  Expect(TokenKind::kRParen, Subclause("13.5.4"));
  call->arg_names.push_back(name_tok.text);
  call->args.push_back(value);
}

Expr* Parser::ParseCompoundAssignExpr(Expr* lhs) {
  auto op_tok = Consume();
  auto* rhs = ParseExpr();
  auto* bin = arena_.Create<Expr>();
  bin->kind = ExprKind::kBinary;
  bin->op = op_tok.kind;
  bin->lhs = lhs;
  bin->rhs = rhs;
  bin->range.start = lhs->range.start;
  return bin;
}

Expr* Parser::ParseParenExpr() {
  Consume();
  auto* lhs = ParseExpr();

  // §11.11: a min:typ:max triplet may be used wherever an expression can
  // appear, so recognize the colon-separated form directly in the general
  // parenthesized-primary path (not only in the delay positions that call
  // ParseMinTypMaxExpr). This lets `(a:b:c)` serve as an operand, e.g.
  // `(a:b:c) + (d:e:f)`.
  if (Check(TokenKind::kColon)) {
    Consume();
    auto* typ = ParseExpr();
    Expect(TokenKind::kColon, Subclause("11.11"));
    auto* max = ParseExpr();
    Expect(TokenKind::kRParen, Subclause("11.11"));
    auto* mtm = arena_.Create<Expr>();
    mtm->kind = ExprKind::kMinTypMax;
    mtm->range.start = lhs->range.start;
    mtm->lhs = lhs;
    mtm->condition = typ;
    mtm->rhs = max;
    mtm->is_parenthesized = true;
    return mtm;
  }

  auto k = CurrentToken().kind;
  bool is_assign = k == TokenKind::kEq || k == TokenKind::kPlusEq ||
                   k == TokenKind::kMinusEq || k == TokenKind::kStarEq ||
                   k == TokenKind::kSlashEq || k == TokenKind::kPercentEq ||
                   k == TokenKind::kAmpEq || k == TokenKind::kPipeEq ||
                   k == TokenKind::kCaretEq || k == TokenKind::kLtLtEq ||
                   k == TokenKind::kGtGtEq || k == TokenKind::kLtLtLtEq ||
                   k == TokenKind::kGtGtGtEq;
  if (is_assign) {
    auto op_tok = Consume();
    auto* rhs = ParseExpr();
    auto* bin = arena_.Create<Expr>();
    bin->kind = ExprKind::kBinary;
    bin->op = op_tok.kind;
    bin->lhs = lhs;
    bin->rhs = rhs;
    bin->range.start = lhs->range.start;
    lhs = bin;
  }
  Expect(TokenKind::kRParen, Subclause("11.5"));

  if (Check(TokenKind::kApostrophe)) {
    Consume();
    Expect(TokenKind::kLParen, Subclause("6.24.1"));
    auto* cast = arena_.Create<Expr>();
    cast->kind = ExprKind::kCast;
    cast->range.start = lhs->range.start;
    cast->lhs = ParseExpr();
    cast->rhs = lhs;
    Expect(TokenKind::kRParen, Subclause("6.24.1"));
    return cast;
  }
  lhs->is_parenthesized = true;
  return lhs;
}

// §6.20 / Syntax 8-2: a parameter_value_assignment may be ordered (a bare
// expression) or named (".name(value)"). Captures one element of either form,
// recording the name in arg_names (empty for the ordered form) and the value in
// elements.
//
// A.4.1.1 makes each element a param_expression (printed page 1194 of
// ~/IEEE 1800-2023.pdf), which A.8.3 lets be a data_type. ParseExpr spells a
// keyword type as a name with its packed dimensions as selects, which the
// elaborator's override readers take, but it cannot spell A.2.2.1's signing
// after an integer type nor a virtual interface type (printed page 1182): `int
// unsigned` stopped at `unsigned` and `virtual ifc` at `virtual`, each
// reported as a missing `)`. An element that opens with `virtual`, or with a
// type keyword that `signed` or `unsigned` follows, is read by ParseDataType
// into a kTypeRef node carrying the type.
void Parser::ParseParamValueAssignment(Expr* base) {
  auto parse_value = [this]() -> Expr* {
    bool opens_a_type = Check(TokenKind::kKwVirtual);
    if (!opens_a_type && IsDataTypeKeyword(CurrentToken().kind)) {
      auto saved = lexer_.SavePos();
      Consume();
      opens_a_type =
          Check(TokenKind::kKwSigned) || Check(TokenKind::kKwUnsigned);
      lexer_.RestorePos(saved);
    }
    if (!opens_a_type) return ParseExpr();
    auto* ref = arena_.Create<Expr>();
    ref->kind = ExprKind::kTypeRef;
    ref->range.start = CurrentLoc();
    ref->type_value = arena_.Create<DataType>(ParseDataType());
    return ref;
  };
  if (Check(TokenKind::kDot)) {
    Consume();
    auto name_tok = Expect(TokenKind::kIdentifier, Subclause("23.10.2.2"));
    Expect(TokenKind::kLParen, Subclause("23.10.2.2"));
    Expr* value = Check(TokenKind::kRParen) ? nullptr : parse_value();
    Expect(TokenKind::kRParen, Subclause("23.10.2.2"));
    base->arg_names.push_back(name_tok.text);
    base->elements.push_back(value);
    return;
  }
  base->arg_names.push_back({});
  base->elements.push_back(parse_value());
}

Expr* Parser::ParseParameterizedScope(Expr* base) {
  Consume();
  if (!Check(TokenKind::kLParen)) return base;
  base->has_param_spec = true;
  Consume();
  if (!Check(TokenKind::kRParen)) {
    ParseParamValueAssignment(base);
    while (Check(TokenKind::kComma)) {
      Consume();
      ParseParamValueAssignment(base);
    }
  }
  Expect(TokenKind::kRParen, Subclause("23.10.2"));
  while (Check(TokenKind::kDot) || Check(TokenKind::kColonColon)) {
    base = MakeMemberAccess(base);
  }
  return base;
}

}  // namespace delta
