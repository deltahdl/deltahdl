#include "parser/parser.h"

namespace delta {

namespace {

// §14.4: the input/output skews parsed for one clocking_item, together with the
// resolved port direction. Bundled so the per-signal builder stays under the
// parameter limit. The output skew fields are only meaningful when the
// direction is not output-only.
struct ClockingItemSkew {
  Direction direction = Direction::kNone;
  Edge in_edge = Edge::kNone;
  Expr* in_delay = nullptr;
  Edge out_edge = Edge::kNone;
  Expr* out_delay = nullptr;
};

// Builds a single clocking signal declaration from the resolved direction/skew
// and the parsed signal name plus optional hierarchical expression.
ClockingSignalDecl MakeClockingSignal(const ClockingItemSkew& skew,
                                      std::string_view name, Expr* hier_expr) {
  ClockingSignalDecl sig;
  sig.direction = skew.direction;
  sig.skew_edge = skew.in_edge;
  sig.skew_delay = skew.in_delay;
  if (skew.direction != Direction::kOutput) {
    sig.out_skew_edge = skew.out_edge;
    sig.out_skew_delay = skew.out_delay;
  }
  sig.name = name;
  sig.hier_expr = hier_expr;
  return sig;
}

}  // namespace

void Parser::ParseClockingSkew(Edge& edge, Expr*& delay) {
  edge = Edge::kNone;
  delay = nullptr;
  if (Match(TokenKind::kKwPosedge)) {
    edge = Edge::kPosedge;
  } else if (Match(TokenKind::kKwNegedge)) {
    edge = Edge::kNegedge;
  } else if (Match(TokenKind::kKwEdge)) {
    edge = Edge::kEdge;
  }
  if (Check(TokenKind::kHash)) {
    Consume();

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

  // §14.7: a clocking block can only be declared inside a module, interface,
  // checker, or program; it shall not be declared inside a package. An
  // anonymous program (§24.9) may legally appear in a package, and a clocking
  // block within that program is itself in a program scope, so the package
  // restriction does not apply there.
  if (package_body_depth_ > 0 && !in_anonymous_program_) {
    diag_.Error(item->loc,
                "a clocking block shall not be declared inside a package");
  }

  if (Match(TokenKind::kKwDefault)) {
    item->is_default_clocking = true;
  } else if (Match(TokenKind::kKwGlobal)) {
    item->is_global_clocking = true;
    if (InGenerateBlock()) {
      diag_.Error(item->loc,
                  "global clocking shall not be declared in a generate block");
    }
  }

  Expect(TokenKind::kKwClocking);

  if (CheckIdentifier()) {
    item->name = Consume().text;
  }

  if (item->is_default_clocking && !item->name.empty() &&
      Check(TokenKind::kSemicolon)) {
    Consume();
    return item;
  }

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

  if (!item->is_global_clocking) ParseClockingItemList(item);

  Expect(TokenKind::kKwEndclocking);
  MatchEndLabel(item->name);
  return item;
}

void Parser::ParseClockingItemList(ModuleItem* item) {
  while (!Check(TokenKind::kKwEndclocking) && !AtEnd()) {
    auto before = lexer_.SavePos().pos;
    ParseClockingItem(item);
    // Guard against a non-clocking_item token (e.g. a missing endclocking, so
    // the enclosing endmodule lands here): ParseClockingItem consumes nothing,
    // so stop and let the caller's Expect report the missing endclocking.
    if (lexer_.SavePos().pos == before) break;
  }
}

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

void Parser::ParseClockingItem(ModuleItem* item) {
  if (Check(TokenKind::kKwDefault)) {
    Consume();
    if (Match(TokenKind::kKwInput)) {
      ParseClockingSkew(item->default_input_skew_edge,
                        item->default_input_skew_delay);
    }
    if (Match(TokenKind::kKwOutput)) {
      ParseClockingSkew(item->default_output_skew_edge,
                        item->default_output_skew_delay);
    }
    Expect(TokenKind::kSemicolon);
    return;
  }

  // The assertion-item alternative of clocking_item may be preceded by
  // attribute instances. Consume them here; they apply to the
  // property/sequence/let declaration that follows.
  bool had_attributes = false;
  if (Check(TokenKind::kAttrStart)) {
    ParseAttributes();
    had_attributes = true;
  }

  if (Check(TokenKind::kKwProperty)) {
    ParsePropertyDecl();
    return;
  }
  if (Check(TokenKind::kKwSequence)) {
    ParseSequenceDecl();
    return;
  }
  if (Check(TokenKind::kKwLet)) {
    ParseLetDecl();
    return;
  }

  if (had_attributes) {
    diag_.Error(CurrentLoc(),
                "expected property, sequence, or let declaration after "
                "attribute instances in clocking block");
    Synchronize();
    return;
  }

  ClockingItemSkew skew;
  skew.direction = ParseClockingDirection(skew.in_edge, skew.in_delay,
                                          skew.out_edge, skew.out_delay);
  if (skew.direction == Direction::kNone) return;

  do {
    std::string_view name = ExpectIdentifier().text;
    Expr* hier_expr = Match(TokenKind::kEq) ? ParseExpr() : nullptr;
    item->clocking_signals.push_back(MakeClockingSignal(skew, name, hier_expr));
  } while (Match(TokenKind::kComma));

  Expect(TokenKind::kSemicolon);
}

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

  if (Check(TokenKind::kKwElse)) {
    Consume();
    stmt->else_branch = ParseStmt();
  } else if (Check(TokenKind::kSemicolon)) {
    Consume();
  } else {
    stmt->then_branch = ParseStmt();
    if (Match(TokenKind::kKwElse)) {
      stmt->else_branch = ParseStmt();
    }
  }
  return stmt;
}

}  // namespace delta
