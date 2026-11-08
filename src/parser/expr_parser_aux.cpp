#include <algorithm>
#include <format>

#include "common/diagnostic.h"
#include "lexer/lexer.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "parser/expr_parser_internal.h"
#include "parser/parser.h"
#include "parser/parser_token_skips.h"

namespace delta {

bool IsNamedLvalue(const Expr* e) {
  while (!e->is_parenthesized &&
         (e->kind == ExprKind::kSelect || e->kind == ExprKind::kMemberAccess)) {
    e = e->kind == ExprKind::kSelect ? e->base : e->lhs;
  }
  return !e->is_parenthesized && e->kind == ExprKind::kIdentifier;
}

namespace {

bool SelectsWithinConcatenation(const Expr* e) {
  if (e->kind != ExprKind::kSelect) return false;
  while (e->kind == ExprKind::kSelect) e = e->base;
  return e->kind == ExprKind::kConcatenation;
}

}  // namespace

bool HasLvalueForm(const Expr* e) {
  if (e->is_parenthesized) return false;
  if (e->kind == ExprKind::kCast) {
    return e->lhs->kind == ExprKind::kAssignmentPattern &&
           HasLvalueForm(e->lhs);
  }
  if (e->kind == ExprKind::kConcatenation ||
      e->kind == ExprKind::kAssignmentPattern) {
    return std::ranges::all_of(e->elements, HasLvalueForm);
  }
  return IsNamedLvalue(e) || SelectsWithinConcatenation(e) ||
         e->kind == ExprKind::kStreamingConcat ||
         e->kind == ExprKind::kReplicate;
}

void CheckIncDecOperand(const Expr* operand, DiagEngine& diag) {
  if (HasLvalueForm(operand)) return;
  diag.Error(operand->range.start,
             "an increment or decrement's operand is a variable_lvalue; this "
             "one is not",
             Subclause("A.8.3"));
}

namespace {

void CheckParenAssignTarget(const Expr* target, DiagEngine& diag) {
  if (HasLvalueForm(target)) return;
  diag.Error(target->range.start,
             "an assignment within an expression assigns a variable_lvalue; "
             "this target is none",
             Subclause("A.6.2"));
}

}  // namespace

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

Expr* Parser::ParseParenExpr() {
  Consume();
  auto* lhs = ParseExpr();

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
    CheckParenAssignTarget(lhs, diag_);
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
  if (is_assign && Check(TokenKind::kDot)) {
    diag_.Error(CurrentLoc(),
                "a method call or member select applies to a primary, and an "
                "assignment in its own parentheses is none; enclose it in a "
                "second pair of parentheses",
                Subclause("A.8.2"));
  }
  return ParseParenMethodTail(lhs);
}

Expr* Parser::ParseParenMethodTail(Expr* paren) {
  if (!Check(TokenKind::kDot)) return paren;
  Expr* result = ParseMethodTail(paren);
  if (result->with_expr == nullptr) return result;
  return ParseWithClauseTail(result);
}

namespace {

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

Expr* Parser::ParseTypeOr(Expr* (Parser::*read)()) {
  if (!OpensTypeAnExpressionCannotSpell(lexer_)) return (this->*read)();
  auto* ref = arena_.Create<Expr>();
  ref->kind = ExprKind::kTypeRef;
  ref->range.start = CurrentLoc();
  DataType dtype;
  if (!TryParseInlineAggregateType(dtype)) dtype = ParseDataType();
  ref->type_value = arena_.Create<DataType>(dtype);
  return ref;
}

void Parser::ParseParamValueAssignment(Expr* base) {
  if (Check(TokenKind::kDot)) {
    Consume();
    auto name_tok = Expect(TokenKind::kIdentifier, Subclause("23.10.2.2"));
    Expect(TokenKind::kLParen, Subclause("23.10.2.2"));
    Expr* value = Check(TokenKind::kRParen)
                      ? nullptr
                      : ParseTypeOr(&Parser::ParseMinTypMaxExpr);
    Expect(TokenKind::kRParen, Subclause("23.10.2.2"));
    base->arg_names.push_back(name_tok.text);
    base->elements.push_back(value);
    return;
  }
  base->arg_names.push_back({});
  base->elements.push_back(ParseTypeOr(&Parser::ParseMinTypMaxExpr));
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

bool ReportUnaryOperatorAfterOperand(const Token& tok, DiagEngine& diag) {
  switch (tok.kind) {
    case TokenKind::kBang:
    case TokenKind::kTilde:
    case TokenKind::kTildeAmp:
    case TokenKind::kTildePipe:
      diag.Error(
          tok.loc,
          std::format("unary operator '{}' cannot follow an operand", tok.text),
          Subclause("5.5"));
      return true;
    default:
      return false;
  }
}

bool EndsExpression(const Token& tok) {
  switch (tok.kind) {
    case TokenKind::kSemicolon:
    case TokenKind::kComma:
    case TokenKind::kColon:
    case TokenKind::kRParen:
    case TokenKind::kRBracket:
    case TokenKind::kRBrace:
      return true;
    default:
      return tok.IsEof();
  }
}

}  // namespace delta
