#include "parser/parser.h"

namespace delta {

// =============================================================================
// §14 — Clocking block declaration
// =============================================================================

// §14.3: Parse clocking skew (edge and/or delay control).
void Parser::ParseClockingSkew(Edge& edge, Expr*& delay) {
  edge = Edge::kNone;
  delay = nullptr;
  if (Match(TokenKind::kKwPosedge)) {
    edge = Edge::kPosedge;
  } else if (Match(TokenKind::kKwNegedge)) {
    edge = Edge::kNegedge;
  }
  if (Check(TokenKind::kHash)) {
    Consume();
    // Handle 1step: integer 1 followed by identifier "step" (§14.4).
    if (Check(TokenKind::kIntLiteral) && CurrentToken().text == "1") {
      auto saved = lexer_.SavePos();
      auto one_tok = CurrentToken();
      Consume();
      if (Check(TokenKind::kIdentifier) && CurrentToken().text == "step") {
        Consume();
        delay = arena_.Create<Expr>();
        delay->kind = ExprKind::kIntegerLiteral;
        delay->text = "1step";
        delay->int_val = 0;
        delay->range.start = one_tok.loc;
      } else {
        lexer_.RestorePos(saved);
        delay = ParsePrimaryExpr();
      }
    } else {
      delay = ParsePrimaryExpr();
    }
  }
}

ModuleItem* Parser::ParseClockingDecl() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kClockingBlock;
  item->loc = CurrentLoc();

  // Handle [default | global] prefix — keyword already peeked by caller.
  if (Match(TokenKind::kKwDefault)) {
    item->is_default_clocking = true;
  } else if (Match(TokenKind::kKwGlobal)) {
    item->is_global_clocking = true;
  }

  Expect(TokenKind::kKwClocking);

  // Optional clocking_identifier (before '@').
  if (CheckIdentifier()) {
    item->name = Consume().text;
  }

  // §14.3: default clocking reference form (name only, no body).
  if (item->is_default_clocking && !item->name.empty() &&
      Check(TokenKind::kSemicolon)) {
    Consume();  // ;
    return item;
  }

  // clocking_event: @identifier or @(event_expression).
  Expect(TokenKind::kAt);
  if (Check(TokenKind::kLParen)) {
    Consume();
    item->clocking_event = ParseEventList();
    Expect(TokenKind::kRParen);
  } else {
    EventExpr ev;
    ev.signal = ParseExpr();
    item->clocking_event.push_back(ev);
  }

  Expect(TokenKind::kSemicolon);

  // Global clocking has no body items.
  if (!item->is_global_clocking) {
    while (!Check(TokenKind::kKwEndclocking) && !AtEnd()) {
      ParseClockingItem(item);
    }
  }

  Expect(TokenKind::kKwEndclocking);
  if (Match(TokenKind::kColon)) ExpectIdentifier();
  return item;
}

// Parse clocking_direction: input/output/inout with optional skews.
Direction Parser::ParseClockingDirection(Edge& in_edge, Expr*& in_delay,
                                         Edge& out_edge, Expr*& out_delay) {
  if (Match(TokenKind::kKwInput)) {
    ParseClockingSkew(in_edge, in_delay);
    if (Match(TokenKind::kKwOutput)) {
      ParseClockingSkew(out_edge, out_delay);
      return Direction::kInout;
    }
    return Direction::kInput;
  }
  if (Match(TokenKind::kKwOutput)) {
    ParseClockingSkew(in_edge, in_delay);
    return Direction::kOutput;
  }
  if (Match(TokenKind::kKwInout)) return Direction::kInout;
  diag_.Error(CurrentLoc(), "expected clocking direction");
  Synchronize();
  return Direction::kNone;
}

// §14.3: Parse a single clocking item (default skew or signal declarations).
void Parser::ParseClockingItem(ModuleItem* item) {
  // Skip default skew declaration for now (not stored).
  if (Check(TokenKind::kKwDefault)) {
    Consume();
    // Consume tokens until semicolon.
    while (!Check(TokenKind::kSemicolon) && !AtEnd()) {
      Consume();
    }
    Expect(TokenKind::kSemicolon);
    return;
  }

  // Parse clocking_direction and optional skews.
  Edge in_edge = Edge::kNone;
  Expr* in_delay = nullptr;
  Edge out_edge = Edge::kNone;
  Expr* out_delay = nullptr;
  Direction dir =
      ParseClockingDirection(in_edge, in_delay, out_edge, out_delay);
  if (dir == Direction::kNone) return;

  // Parse comma-separated signal declarations with optional assignments.
  do {
    ClockingSignalDecl sig;
    sig.direction = dir;
    sig.skew_edge = in_edge;
    sig.skew_delay = in_delay;
    if (dir != Direction::kOutput) {
      sig.out_skew_edge = out_edge;
      sig.out_skew_delay = out_delay;
    }
    sig.name = ExpectIdentifier().text;
    if (Match(TokenKind::kEq)) {
      sig.hier_expr = ParseExpr();
    }
    item->clocking_signals.push_back(sig);
  } while (Match(TokenKind::kComma));

  Expect(TokenKind::kSemicolon);
}

// =============================================================================
// §15.5.4 — wait_order statement
// =============================================================================

Stmt* Parser::ParseWaitOrderStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kWaitOrder;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwWaitOrder);
  Expect(TokenKind::kLParen);

  stmt->wait_order_events.push_back(ParseExpr());
  while (Match(TokenKind::kComma)) {
    stmt->wait_order_events.push_back(ParseExpr());
  }
  Expect(TokenKind::kRParen);

  // §15.5.4: Parse optional action block (pass/else statements).
  if (Check(TokenKind::kKwElse)) {
    Consume();
    stmt->else_branch = ParseStmt();
  } else if (Check(TokenKind::kSemicolon)) {
    Consume();  // Null action.
  } else {
    stmt->then_branch = ParseStmt();
    if (Match(TokenKind::kKwElse)) {
      stmt->else_branch = ParseStmt();
    }
  }
  return stmt;
}

}  // namespace delta
