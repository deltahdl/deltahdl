#include "common/diagnostic.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "parser/expr_parser_internal.h"
#include "parser/parser.h"

namespace delta {

Stmt* Parser::ParseCycleDelayStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kCycleDelay;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kHashHash, Subclause("14.11"));
  if (Check(TokenKind::kLParen)) {
    Consume();
    stmt->cycle_delay = ParseExpr();
    Expect(TokenKind::kRParen, Subclause("14.11"));
  } else {
    stmt->cycle_delay = ParsePrimaryExpr();
    CheckUnparenthesizedCycleDelay(stmt->cycle_delay, diag_);
  }
  stmt->body = ParseStmt();
  return stmt;
}

static bool IsLoneIdentifier(const Expr* e) {
  return e->kind == ExprKind::kIdentifier && e->scope_prefix.empty() &&
         e->text != "$" && e->text != "null";
}

bool IsPsIdentifier(const Expr* e) {
  if (e->kind == ExprKind::kMemberAccess && e->is_scope_resolution) {
    return IsLoneIdentifier(e->lhs);
  }
  return IsLoneIdentifier(e) ||
         (e->kind == ExprKind::kIdentifier && e->scope_prefix == "$unit");
}

void CheckUnparenthesizedCycleDelay(const Expr* e, DiagEngine& diag) {
  if (e->kind == ExprKind::kIntegerLiteral || IsLoneIdentifier(e)) return;
  diag.Error(e->range.start,
             "a cycle delay written without parentheses is an integral number "
             "or an identifier; any other expression is parenthesized",
             Subclause("A.6.11"));
}

Stmt* Parser::ParseDelayStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kDelay;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kHash, Subclause("9.4.1"));

  if (Check(TokenKind::kLParen)) {
    Consume();
    stmt->delay = ParseMinTypMaxExpr();
    Expect(TokenKind::kRParen, Subclause("9.4.1"));
  } else {
    stmt->delay = ParseDelayValue();
  }
  stmt->body = ParseStmt();
  return stmt;
}

EventExpr Parser::ParseNamedClockingEvent() {
  EventExpr ev;
  Token first = CurrentToken();
  if (first.Is(TokenKind::kSystemIdentifier) && first.text == "$global_clock") {
    ev.signal = ParseSystemCall();
    return ev;
  }
  if (first.Is(TokenKind::kSystemIdentifier) && first.text == "$root") {
    Consume();
  } else {
    first = ExpectIdentifier(Subclause("9.4.2"));
  }
  Expr* name = ParseMemberAccessChain(first);
  bool ends_in_select = false;
  while (AtSelectBracket()) {
    name = ParseSelectExpr(name);
    ends_in_select = true;
    while (Check(TokenKind::kDot) || Check(TokenKind::kColonColon)) {
      name = MakeMemberAccess(name);
      ends_in_select = false;
    }
  }
  if (ends_in_select) {
    diag_.Error(name->range.start,
                "an unparenthesized clocking event is '@' and a name; an "
                "expression is parenthesized",
                Subclause("A.6.5"));
  }
  ev.signal = name;
  return ev;
}

Stmt* Parser::ParseEventControlStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kEventControl;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kAt, Subclause("9.4.2"));
  if (Match(TokenKind::kStar)) {
    stmt->is_star_event = true;
  } else if (Check(TokenKind::kLParen)) {
    Consume();
    if (Match(TokenKind::kStar)) {
      stmt->is_star_event = true;
    } else {
      stmt->events = ParseEventList();
    }
    Expect(TokenKind::kRParen, Subclause("9.4.2"));
  } else {
    stmt->events.push_back(ParseNamedClockingEvent());
  }
  stmt->body = ParseStmt();
  return stmt;
}

}  // namespace delta
