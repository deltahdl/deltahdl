#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/operator_binding_power.h"
#include "parser/parser.h"
#include "parser/parser_constraint_items_internal.h"

namespace delta {

void ParserConstraintItemHelpers::Capture(Parser& p, ClassMember* member) {
  if (member == nullptr) return;
  auto saved = p.lexer_.SavePos();
  p.diag_.PushSuppress();
  std::vector<ConstraintItem*> items;
  const bool kParsed = ParseItemsToBrace(p, items);
  p.diag_.PopSuppress();
  p.lexer_.RestorePos(saved);
  if (!kParsed) return;
  member->constraint_items = std::move(items);
  member->constraint_items_parsed = true;
}

// The items of a block or a braced constraint_set through its '}'.
bool ParserConstraintItemHelpers::ParseItemsToBrace(
    Parser& p, std::vector<ConstraintItem*>& out) {
  while (!p.Match(TokenKind::kRBrace)) {
    if (p.AtEnd()) return false;
    ConstraintItem* item = ParseExpressionItem(p);
    if (item == nullptr) return false;
    out.push_back(item);
  }
  return true;
}

// A.1.10: one constraint_block_item, told apart by the keyword it opens with;
// null where it does not parse.
ConstraintItem* ParserConstraintItemHelpers::ParseExpressionItem(Parser& p) {
  auto* item = p.arena_.Create<ConstraintItem>();
  bool parsed = false;
  if (p.Match(TokenKind::kKwIf)) {
    parsed = ParseIfElse(p, *item);
  } else if (p.Match(TokenKind::kKwForeach)) {
    parsed = ParseForeach(p, *item);
  } else if (p.Match(TokenKind::kKwUnique)) {
    parsed = ParseUnique(p, *item);
  } else if (p.Match(TokenKind::kKwSolve)) {
    parsed = ParseSolveBefore(p, *item);
  } else if (p.Match(TokenKind::kKwDisable)) {
    // §18.5.13.2: disable soft constraint_primary ;
    item->kind = ConstraintItemKind::kDisableSoft;
    item->expr = p.Match(TokenKind::kKwSoft) ? p.ParseExpr() : nullptr;
    parsed = item->expr != nullptr && p.Match(TokenKind::kSemicolon);
  } else {
    item->soft = p.Match(TokenKind::kKwSoft);
    parsed = ParseExpressionOrDist(p, *item);
  }
  return parsed ? item : nullptr;
}

// A.1.10: a constraint_set, a braced list of constraint expressions or one
// constraint expression alone.
bool ParserConstraintItemHelpers::ParseSet(Parser& p,
                                           std::vector<ConstraintItem*>& out) {
  if (p.Match(TokenKind::kLBrace)) return ParseItemsToBrace(p, out);
  ConstraintItem* item = ParseExpressionItem(p);
  if (item == nullptr) return false;
  out.push_back(item);
  return true;
}

// §18.5.6: if ( expression ) constraint_set [ else constraint_set ], an else
// binding to the closest if before it.
bool ParserConstraintItemHelpers::ParseIfElse(Parser& p, ConstraintItem& item) {
  item.kind = ConstraintItemKind::kIfElse;
  if (!p.Match(TokenKind::kLParen)) return false;
  item.expr = p.ParseExpr();
  if (item.expr == nullptr || !p.Match(TokenKind::kRParen)) return false;
  if (!ParseSet(p, item.body)) return false;
  item.has_else = p.Match(TokenKind::kKwElse);
  return !item.has_else || ParseSet(p, item.else_body);
}

// §18.5.7.1: foreach ( array [ loop_variables ] ) constraint_set, a loop
// variable left out keeping its place as an empty name.
bool ParserConstraintItemHelpers::ParseForeach(Parser& p,
                                               ConstraintItem& item) {
  item.kind = ConstraintItemKind::kForeach;
  if (!p.Match(TokenKind::kLParen)) return false;
  if (!p.CheckIdentifier() && !p.Check(TokenKind::kKwThis)) return false;
  item.expr = p.ParseMemberAccessChain(p.Consume());
  if (!p.Match(TokenKind::kLBracket)) return false;
  do {
    item.loop_vars.push_back(p.CheckIdentifier() ? p.Consume().text
                                                 : std::string_view());
  } while (p.Match(TokenKind::kComma));
  if (!p.Match(TokenKind::kRBracket) || !p.Match(TokenKind::kRParen)) {
    return false;
  }
  return ParseSet(p, item.body);
}

// §18.5.4: unique { range_list } ;
bool ParserConstraintItemHelpers::ParseUnique(Parser& p, ConstraintItem& item) {
  item.kind = ConstraintItemKind::kUnique;
  if (!p.Match(TokenKind::kLBrace)) return false;
  do {
    Expr* range = p.ParseInsideValueRange();
    if (range == nullptr) return false;
    item.exprs.push_back(range);
  } while (p.Match(TokenKind::kComma));
  return p.Match(TokenKind::kRBrace) && p.Match(TokenKind::kSemicolon);
}

// §18.5.9: solve solve_before_list before solve_before_list ;
bool ParserConstraintItemHelpers::ParseSolveBefore(Parser& p,
                                                   ConstraintItem& item) {
  item.kind = ConstraintItemKind::kSolveBefore;
  return ParseExprList(p, item.exprs) && p.Match(TokenKind::kKwBefore) &&
         ParseExprList(p, item.after) && p.Match(TokenKind::kSemicolon);
}

// §18.5.5 and §18.5.3: an expression followed by `->` and the constraint_set
// it implies, or an expression_or_dist through its ';'. The antecedent is read
// at a binding power just above the implication's own, so it stops at the
// `->`; written `soft`, the item is an expression_or_dist alone.
bool ParserConstraintItemHelpers::ParseExpressionOrDist(Parser& p,
                                                        ConstraintItem& item) {
  if (!item.soft) {
    auto saved = p.lexer_.SavePos();
    Expr* antecedent =
        p.ParseExprBp(InfixBindingPower(TokenKind::kArrow).first + 1);
    if (antecedent != nullptr && p.Match(TokenKind::kArrow)) {
      item.kind = ConstraintItemKind::kImplication;
      item.expr = antecedent;
      return ParseSet(p, item.body);
    }
    p.lexer_.RestorePos(saved);
  }
  item.expr = p.ParseExpr();
  if (item.expr == nullptr) return false;
  if (p.Match(TokenKind::kKwDist) && !ParseDistList(p, item)) return false;
  return p.Match(TokenKind::kSemicolon);
}

// §18.5.3: the braced dist_list after `dist`.
bool ParserConstraintItemHelpers::ParseDistList(Parser& p,
                                                ConstraintItem& item) {
  item.has_dist = true;
  if (!p.Match(TokenKind::kLBrace)) return false;
  do {
    ConstraintDistItem dist_item;
    if (!p.ParseDistItem(dist_item)) return false;
    item.dist.push_back(dist_item);
  } while (p.Match(TokenKind::kComma));
  return p.Match(TokenKind::kRBrace);
}

// A comma separated list of expressions.
bool ParserConstraintItemHelpers::ParseExprList(Parser& p,
                                                std::vector<Expr*>& out) {
  do {
    Expr* expr = p.ParseExpr();
    if (expr == nullptr) return false;
    out.push_back(expr);
  } while (p.Match(TokenKind::kComma));
  return true;
}

}  // namespace delta
