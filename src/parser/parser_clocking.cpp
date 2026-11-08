#include <string_view>

#include "common/diagnostic.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "parser/expr_parser_internal.h"
#include "parser/parser.h"

namespace delta {

namespace {

struct ClockingItemSkew {
  Direction direction = Direction::kNone;
  Edge in_edge = Edge::kNone;
  Expr* in_delay = nullptr;
  Edge out_edge = Edge::kNone;
  Expr* out_delay = nullptr;
};

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

    if (Check(TokenKind::kLParen)) {
      delay = ParsePrimaryExpr();
    } else {
      delay = ParseDelayValue();
    }
  }
}

ModuleItem* Parser::ParseClockingDecl() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kClockingBlock;
  item->loc = CurrentLoc();

  if (package_body_depth_ > 0) {
    diag_.Error(item->loc, "a package body cannot hold a clocking block",
                Subclause("14.7"));
  }

  if (Match(TokenKind::kKwDefault)) {
    item->is_default_clocking = true;
  } else if (Match(TokenKind::kKwGlobal)) {
    item->is_global_clocking = true;
    if (InGenerateBlock()) {
      diag_.Error(item->loc,
                  "a generate block cannot hold a global clocking declaration",
                  Subclause("14.14"));
    }
  }

  Expect(TokenKind::kKwClocking, Subclause("14.3"));

  if (CheckIdentifier()) {
    item->name = Consume().text;
  }

  if (item->is_default_clocking && !item->name.empty() &&
      Check(TokenKind::kSemicolon)) {
    Consume();
    return item;
  }

  Expect(TokenKind::kAt, Subclause("14.3"));
  if (Check(TokenKind::kLParen)) {
    Consume();
    item->clocking_event = ParseEventList();
    Expect(TokenKind::kRParen, Subclause("14.3"));
  } else {
    item->clocking_event.push_back(ParseNamedClockingEvent());
  }

  Expect(TokenKind::kSemicolon, Subclause("14.3"));

  if (!item->is_global_clocking) ParseClockingItemList(item);

  Expect(TokenKind::kKwEndclocking, Subclause("14.3"));
  MatchEndLabel(item->name);
  return item;
}

bool Parser::AtClockingDecl() {
  if (Check(TokenKind::kKwClocking)) return true;
  if (!Check(TokenKind::kKwDefault) && !Check(TokenKind::kKwGlobal)) {
    return false;
  }
  auto saved = lexer_.SavePos();
  Consume();
  bool is_clocking = Check(TokenKind::kKwClocking);
  lexer_.RestorePos(saved);
  return is_clocking;
}

void Parser::RejectClockingDecl(std::string_view message) {
  diag_.Error(CurrentLoc(), std::string(message), Subclause("14.7"));
  ParseClockingDecl();
}

void Parser::ParseClockingItemList(ModuleItem* item) {
  while (!Check(TokenKind::kKwEndclocking) && !AtEnd()) {
    if (AtClockingDecl()) {
      RejectClockingDecl("a clocking block cannot hold another clocking block");
      continue;
    }
    auto before = lexer_.SavePos().pos;
    ParseClockingItem(item);
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
  diag_.Error(CurrentLoc(), "expected clocking direction", Subclause("14.3"));
  Synchronize();
  return Direction::kNone;
}

void Parser::ParseClockingDefaultSkew(const Token& direction, Edge& edge,
                                      Expr*& delay) {
  ParseClockingSkew(edge, delay);
  if (edge != Edge::kNone || delay != nullptr) return;
  diag_.Error(direction.loc,
              "default " + std::string(direction.text) +
                  " skew names no clocking_skew: an edge, a delay, or both",
              Subclause("A.6.11"));
}

void Parser::ParseClockingDefaultSkews(ModuleItem* item) {
  auto default_tok = Consume();
  bool has_direction = false;
  if (Check(TokenKind::kKwInput)) {
    has_direction = true;
    ParseClockingDefaultSkew(Consume(), item->default_input_skew_edge,
                             item->default_input_skew_delay);
  }
  if (Check(TokenKind::kKwOutput)) {
    has_direction = true;
    ParseClockingDefaultSkew(Consume(), item->default_output_skew_edge,
                             item->default_output_skew_delay);
    if (Check(TokenKind::kKwInput)) {
      diag_.Error(CurrentLoc(),
                  "default skew writes the input skew before the output skew",
                  Subclause("A.6.11"));
      ParseClockingDefaultSkew(Consume(), item->default_input_skew_edge,
                               item->default_input_skew_delay);
    }
  }
  if (!has_direction) {
    diag_.Error(default_tok.loc,
                "default clocking item takes an input skew, an output skew, or "
                "both",
                Subclause("A.6.11"));
  }
  Expect(TokenKind::kSemicolon, Subclause("14.4"));
}

void Parser::CheckClockingBlockDecl(const ModuleItem* decl,
                                    std::string_view kind) {
  if (decl == nullptr) return;
  bool multiclocked =
      decl->decl_clock_event_count >= 2 ||
      (decl->decl_clock_event_count == 1 && !decl->decl_has_leading_clock);
  if (multiclocked) {
    diag_.Error(decl->loc,
                "a multiclocked " + std::string(kind) +
                    " is not allowed in a clocking block",
                Subclause("16.16"));
  } else if (decl->decl_has_leading_clock) {
    diag_.Error(decl->loc,
                "a " + std::string(kind) +
                    " declared in a clocking block may not specify an "
                    "explicit clocking event",
                Subclause("16.16"));
  }
}

void Parser::ParseClockingItem(ModuleItem* item) {
  if (Check(TokenKind::kKwDefault)) {
    ParseClockingDefaultSkews(item);
    return;
  }

  bool had_attributes = false;
  if (Check(TokenKind::kAttrStart)) {
    ParseAttributes();
    had_attributes = true;
  }

  if (Check(TokenKind::kKwProperty)) {
    ModuleItem* decl = ParsePropertyDecl();
    CheckClockingBlockDecl(decl, "property");
    if (decl != nullptr) item->clocking_decls.push_back(decl);
    return;
  }
  if (Check(TokenKind::kKwSequence)) {
    ModuleItem* decl = ParseSequenceDecl();
    CheckClockingBlockDecl(decl, "sequence");
    if (decl != nullptr) item->clocking_decls.push_back(decl);
    return;
  }
  if (Check(TokenKind::kKwLet)) {
    ParseLetDecl();
    return;
  }

  if (had_attributes) {
    diag_.Error(CurrentLoc(),
                "expected property, sequence, or let declaration after "
                "attribute instances in clocking block",
                Subclause("14.3"));
    Synchronize();
    return;
  }

  ClockingItemSkew skew;
  skew.direction = ParseClockingDirection(skew.in_edge, skew.in_delay,
                                          skew.out_edge, skew.out_delay);
  if (skew.direction == Direction::kNone) return;

  do {
    std::string_view name = ExpectIdentifier(Subclause("14.3")).text;
    Expr* hier_expr = Match(TokenKind::kEq) ? ParseExpr() : nullptr;
    item->clocking_signals.push_back(MakeClockingSignal(skew, name, hier_expr));
  } while (Match(TokenKind::kComma));

  Expect(TokenKind::kSemicolon, Subclause("14.3"));
}

static bool IsBitSelect(const Expr* e) {
  return e->kind == ExprKind::kSelect && e->index_end == nullptr;
}

bool IsHierarchicalName(const Expr* e, bool trailing_select) {
  while (trailing_select && IsBitSelect(e)) e = e->base;
  while (e->kind == ExprKind::kMemberAccess && !e->is_scope_resolution) {
    e = e->lhs;
    while (IsBitSelect(e)) e = e->base;
  }
  return e->kind == ExprKind::kIdentifier && e->scope_prefix != "$unit";
}

Expr* Parser::ParseWaitOrderOperand() {
  Expr* e = ParseExpr();
  if (e != nullptr && !IsHierarchicalName(e, false)) {
    diag_.Error(e->range.start,
                "wait_order operand shall be a hierarchical identifier",
                Subclause("15.5.4"));
  }
  return e;
}

}  // namespace delta
