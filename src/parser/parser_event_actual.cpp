#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/lexer.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/expr_substitute.h"
#include "parser/parser.h"
#include "parser/parser_property_spec_internal.h"

namespace delta {

Expr* ParserPropertySpecHelpers::ParseEventActualOperand(Parser& p) {
  const SourceLoc kLoc = p.CurrentLoc();
  if (!p.Check(TokenKind::kLParen) || !p.OpensEventGroup(false)) {
    return EventAsActual(p.ParseSingleEvent(), kLoc, p.arena_);
  }
  p.Consume();
  Expr* event = ParseEventActualOperand(p);
  while (p.Match(TokenKind::kKwOr) || p.Match(TokenKind::kComma)) {
    event = EitherEventActual(event, ParseEventActualOperand(p), p.arena_);
  }
  p.Expect(TokenKind::kRParen, Subclause("9.4"));
  return event;
}

Expr* ParserPropertySpecHelpers::ParseEventActual(Parser& p) {
  Expr* event = ParseEventActualOperand(p);
  while (p.Match(TokenKind::kKwOr)) {
    event = EitherEventActual(event, ParseEventActualOperand(p), p.arena_);
  }
  return event;
}

bool ParserPropertySpecHelpers::AheadListsNamesOnly(Parser& p) {
  auto saved = p.lexer_.SavePos();
  p.Consume();
  int names = 0;
  bool name = false;
  do {
    name = p.Match(TokenKind::kIdentifier);
    while (name &&
           (p.Match(TokenKind::kDot) || p.Match(TokenKind::kColonColon))) {
      name = p.Match(TokenKind::kIdentifier);
    }
    ++names;
  } while (name && p.Match(TokenKind::kComma));
  const bool kListed = name && names > 1 && p.Check(TokenKind::kRParen);
  p.lexer_.RestorePos(saved);
  return kListed;
}

Expr* ParserPropertySpecHelpers::ParseListedNamesActual(Parser& p) {
  if (!p.Check(TokenKind::kLParen) || !AheadListsNamesOnly(p)) return nullptr;
  auto saved = p.lexer_.SavePos();
  PropertyExprNode* sequence = ParseWholeSequenceActual(p);
  p.lexer_.RestorePos(saved);
  Expr* events = ParseEventActual(p);
  if (!p.Check(TokenKind::kComma) && !p.Check(TokenKind::kRParen)) {
    p.lexer_.RestorePos(saved);
    return nullptr;
  }
  events->sequence_reading = sequence;
  return events;
}

}  // namespace delta
