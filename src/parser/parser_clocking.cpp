#include "parser/parser.h"

namespace delta {

// =============================================================================
// §14 — Clocking block declaration
// =============================================================================

// clocking_skew ::= edge_identifier [delay_control] | delay_control
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
    delay = ParsePrimaryExpr();
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

// Parse one clocking_item:
//   default default_skew ;
//   | clocking_direction list_of_clocking_decl_assign ;
void Parser::ParseClockingItem(ModuleItem* item) {
  // Skip "default default_skew ;" for now (not stored).
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
  Direction dir = Direction::kNone;
  Edge in_edge = Edge::kNone;
  Expr* in_delay = nullptr;
  Edge out_edge = Edge::kNone;
  Expr* out_delay = nullptr;

  if (Match(TokenKind::kKwInput)) {
    dir = Direction::kInput;
    ParseClockingSkew(in_edge, in_delay);
    // Check for combined: input [skew] output [skew]
    if (Match(TokenKind::kKwOutput)) {
      dir = Direction::kInout;  // Combined input+output
      ParseClockingSkew(out_edge, out_delay);
    }
  } else if (Match(TokenKind::kKwOutput)) {
    dir = Direction::kOutput;
    ParseClockingSkew(in_edge, in_delay);
  } else if (Match(TokenKind::kKwInout)) {
    dir = Direction::kInout;
  } else {
    diag_.Error(CurrentLoc(), "expected clocking direction");
    Synchronize();
    return;
  }

  // list_of_clocking_decl_assign: signal [= expr] {, signal [= expr]}
  do {
    ClockingSignalDecl sig;
    sig.direction = dir;
    if (dir == Direction::kOutput) {
      sig.skew_edge = in_edge;
      sig.skew_delay = in_delay;
    } else {
      sig.skew_edge = in_edge;
      sig.skew_delay = in_delay;
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

  // action_block: statement_or_null | [statement] else statement_or_null
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
