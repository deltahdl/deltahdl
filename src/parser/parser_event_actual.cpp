#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/lexer.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/expr_substitute.h"
#include "parser/parser.h"
#include "parser/parser_property_spec_internal.h"

namespace delta {

// §9.4 Syntax 9-4: one event of an event actual, with any iff guard, or a
// parenthesized event expression, whose events a `,` joins as an `or` does
// (§9.4.2.1), kept as EventAsActual and EitherEventActual write them.
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

// §16.8.1 b) and §9.4.2: an event expression opening with an edge keyword or
// with a parenthesized group of events (footnote 36 to Syntax 9-4), given as
// the actual argument of a formal of type event: its events joined by `or`,
// a `,` joining them only within the parentheses, outside which it ends the
// actual.
Expr* ParserPropertySpecHelpers::ParseEventActual(Parser& p) {
  Expr* event = ParseEventActualOperand(p);
  while (p.Match(TokenKind::kKwOr)) {
    event = EitherEventActual(event, ParseEventActualOperand(p), p.arena_);
  }
  return event;
}

// §9.4 with §16.11: whether a parenthesized list of two or more names, plain,
// scoped or a member's, `(a, b)`, is ahead. It reads as an event expression,
// the `or` of its names' events, and as a sequence calling the names after
// the first at its match, A.8.2 writing a call's list of arguments as
// optional; ParseListedNamesActual reads it both ways. The lexer is rewound.
bool ParserPropertySpecHelpers::AheadListsNamesOnly(Parser& p) {
  auto saved = p.lexer_.SavePos();
  p.Consume();  // (
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

// §16.8.1: an actual that is a parenthesized list of names, `(a, f)`, is the
// event list or the sequence it reads as by the formal it binds to, which the
// parse does not know. So it is read as the event list, which needs no
// subroutine of those names, with the sequence kept as its
// sequence_reading, for a formal used as a sequence. Null, the lexer rewound,
// where no such list is ahead or its event list does not end the actual:
// `(a, f) ##1 b` is a sequence alone.
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
