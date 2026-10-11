#include "common/diagnostic.h"
#include "common/source_loc.h"
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

}  // namespace delta
