#include "common/diagnostic.h"
#include "lexer/lexer.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "parser/expr_parser_internal.h"
#include "parser/parser.h"
#include "parser/parser_token_skips.h"

namespace delta {

// Answers whether the token standing after `new` opens a shallow-copy source.
// A.2.4 gives class_new the two alternatives
// `[ class_scope ] new [ ( list_of_arguments ) ]` and `new expression`, and
// footnote 23 on that production requires the second's expression to yield an
// object handle. Two tokens can open one. An identifier can name a
// handle variable, and `this` is one outright: §8.11 makes it a predefined
// object handle to the object the enclosing subroutine was invoked on.
//
// No third token is admitted, because the two that remain belong to the other
// productions. A '(' after `new` is the first alternative's list_of_arguments,
// which is what distinguishes the two alternatives at all. A '[' is
// dynamic_array_new, `new [ expression ] [ ( expression ) ]` in A.2.4, and
// Parser::ParseNewExpr reads it before asking this.
//
// Parser::ParseNewExpr and Parser::MakeMemberAccess both ask, and have to
// agree: the first decides what `new` takes as a copy source, and the second
// reports §8.12's ban on a typed constructor call making a shallow copy over
// the same source when a class scope precedes the `new`. A source one admits
// and the other does not is either accepted with the class scope or left
// standing where a statement terminator belongs.
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

  // A.8.1's slice_size is a simple_type or a constant_expression. A lone name
  // or type keyword before the stream's brace is kept as a name, for the later
  // stages to size as a type or read as a parameter. A lone number is the
  // literal ParsePrimaryExpr makes of it, so its base is read with its digits
  // (§11.4.14.2): spelled as a name, 8'd8 was read as 88. Anything else is an
  // expression running up to the brace, which continues no operand: read as
  // one primary, `W*2` stopped at the `*`.
  if (!Check(TokenKind::kLBrace)) {
    auto saved = lexer_.SavePos();
    auto tok = Consume();
    bool is_number = tok.kind == TokenKind::kIntLiteral ||
                     tok.kind == TokenKind::kUnbasedUnsizedLiteral;
    if (!is_number && Check(TokenKind::kLBrace)) {
      auto* type_id = arena_.Create<Expr>();
      type_id->kind = ExprKind::kIdentifier;
      type_id->text = tok.text;
      type_id->range.start = tok.loc;
      sc->lhs = type_id;
    } else {
      lexer_.RestorePos(saved);
      sc->lhs = ParseExpr();
    }
  }

  // A.8.1's stream_expression is an expression and then, optionally, `with [
  // array_range_expression ]`, the range applying to the whole operand. The
  // operand is read short of Parser::ParseExpr, which reports a range after
  // any other expression, and the range is read here into Expr::stream_range,
  // apart from a with clause the operand carries itself. Footnote 40 keeps
  // `{}` out of a stream.
  Expect(TokenKind::kLBrace, Subclause("11.4.14"));
  do {
    Expr* operand = ParseExprBp(0);
    ReportPredicateOperator(operand, diag_);
    if (WithOpensRange(lexer_)) {
      operand->stream_range = ParseWithClauseRange(true);
    }
    sc->elements.push_back(operand);
  } while (Match(TokenKind::kComma));
  ReportEmptyConcatItems(sc, diag_);
  Expect(TokenKind::kRBrace, Subclause("11.4.14"));
  return sc;
}

// A.8.2's `( list_of_arguments )` of a subroutine call or a class_new: the
// list is ordered and then named, or named from its first element, and either
// may be empty. Each argument lands in call->args, and a named one records its
// name in call->arg_names as well.
// A.8.4 (printed page 1211): `primary` has no class_new or dynamic_array_new
// alternative, and A.6.2 (printed page 1198) admits each only as the
// right-hand side of a blocking assignment, so neither is an expression and
// neither can be an argument. ParsePrimaryExpr reads `new` wherever an
// expression starts, for the assignment forms it stands in, so an argument is
// told apart here: `q.push_back(new(7))` was accepted and pushed a null handle.
bool IsNewExpr(const Expr* arg) {
  return arg != nullptr && arg->kind == ExprKind::kCall && arg->text == "new" &&
         arg->callee.empty();
}

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
  for (const Expr* arg : call->args) {
    if (IsNewExpr(arg)) {
      diag_.Error(arg->range.start,
                  "'new' is not an expression and cannot be a subroutine "
                  "argument",
                  Subclause("A.8.4"));
    }
  }
}

// A.8.2's named arguments, `. identifier ( [ expression ] )` each, separated
// by commas, which follow a call's positional ones.
void Parser::ParseTrailingNamedArgs(Expr* call) {
  do {
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
  } while (Match(TokenKind::kComma));
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
  // A.8.2 roots a method call in a primary, and A.8.3 makes an assignment an
  // expression only in its own parentheses, so `(h = g)` is no primary and
  // takes no method or member; `((h = g))` is one, a parenthesized
  // expression (A.8.4), and does.
  if (is_assign && Check(TokenKind::kDot)) {
    diag_.Error(CurrentLoc(),
                "a method call or member select applies to a primary, and an "
                "assignment in its own parentheses is none; enclose it in a "
                "second pair of parentheses",
                Subclause("A.8.2"));
  }
  return ParseParenMethodTail(lhs);
}

// A.8.2 makes a method_call's root a primary and A.8.4 counts a parenthesized
// mintypmax_expression among the primaries, so a method is called on the handle
// a parenthesized expression yields (§8.4), `(sel ? x : y).f()`. The call
// takes the tail a cast's does, with the with clause a randomize_call or an
// array_manipulation_call ends in. Parser::ParseConcatenation reads the same
// tail after a concatenation, a multiple concatenation, the empty unpacked
// array concatenation and a streaming concatenation, the other primaries A.8.4
// lists that end in a bracket.
Expr* Parser::ParseParenMethodTail(Expr* paren) {
  if (!Check(TokenKind::kDot)) return paren;
  Expr* result = ParseMethodTail(paren);
  if (result->with_expr == nullptr) return result;
  return ParseWithClauseTail(result);
}

namespace {

// Whether the lexer stands at a data_type of A.2.2.1 that ParseExpr cannot
// spell as a name with its packed dimensions as selects: one opening with
// struct, union, enum, virtual, chandle or event, or a type keyword that
// `signed` or `unsigned` follows.
bool OpensTypeAnExpressionCannotSpell(Lexer& lexer) {
  switch (lexer.Peek().kind) {
    case TokenKind::kKwStruct:
    case TokenKind::kKwUnion:
    case TokenKind::kKwEnum:
    case TokenKind::kKwVirtual:
    case TokenKind::kKwChandle:
    case TokenKind::kKwEvent:
      return true;
    default:
      break;
  }
  if (!IsDataTypeKeyword(lexer.Peek().kind)) return false;
  Lexer::SavedPos saved = lexer.SavePos();
  lexer.Next();
  const TokenKind kNext = lexer.Peek().kind;
  lexer.RestorePos(saved);
  return kNext == TokenKind::kKwSigned || kNext == TokenKind::kKwUnsigned;
}

}  // namespace

// A data_type where one is admitted beside an expression -- A.8.3's
// param_expression, a system call's first argument (A.8.2) -- that ParseExpr
// cannot spell, read by ParseDataType into a kTypeRef node carrying it in
// Expr::type_value, the node `type(data_type)` makes; anything else is read by
// `read`. ParseExpr spells a keyword type as a name with its packed
// dimensions as selects, which the readers of such an argument take, so `int
// unsigned` stopped at `unsigned` and `struct packed { ... }` at `struct`.
Expr* Parser::ParseTypeOr(Expr* (Parser::*read)()) {
  if (!OpensTypeAnExpressionCannotSpell(lexer_)) return (this->*read)();
  auto* ref = arena_.Create<Expr>();
  ref->kind = ExprKind::kTypeRef;
  ref->range.start = CurrentLoc();
  ref->type_value = arena_.Create<DataType>(ParseDataType());
  return ref;
}

// §6.20 / Syntax 8-2: a parameter_value_assignment may be ordered (a bare
// expression) or named (".name(value)"). Captures one element of either form,
// recording the name in arg_names (empty for the ordered form) and the value in
// elements. A.4.1.1 makes each element a param_expression (printed page 1194
// of IEEE 1800-2023), which A.8.3 lets be a data_type, read by ParseTypeOr.
void Parser::ParseParamValueAssignment(Expr* base) {
  if (Check(TokenKind::kDot)) {
    Consume();
    auto name_tok = Expect(TokenKind::kIdentifier, Subclause("23.10.2.2"));
    Expect(TokenKind::kLParen, Subclause("23.10.2.2"));
    Expr* value =
        Check(TokenKind::kRParen) ? nullptr : ParseTypeOr(&Parser::ParseExpr);
    Expect(TokenKind::kRParen, Subclause("23.10.2.2"));
    base->arg_names.push_back(name_tok.text);
    base->elements.push_back(value);
    return;
  }
  base->arg_names.push_back({});
  base->elements.push_back(ParseTypeOr(&Parser::ParseExpr));
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
