#include <cstdint>
#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/expr_parser_internal.h"
#include "parser/operator_binding_power.h"
#include "parser/parser.h"
#include "parser/parser_constraint_items_internal.h"

namespace delta {

namespace {

bool IsPrimaryName(const Expr* e) {
  if (e == nullptr) return false;
  switch (e->kind) {
    case ExprKind::kMemberAccess:
      return IsPrimaryName(e->lhs);
    case ExprKind::kSelect:
      return IsPrimaryName(e->base);
    default:
      return e->kind == ExprKind::kIdentifier;
  }
}

}  // namespace

void ParserConstraintItemHelpers::ReportLocalQualifiers(Parser& p) {
  auto saved = p.lexer_.SavePos();
  for (int depth = 1; depth > 0 && !p.AtEnd(); p.Consume()) {
    if (p.Check(TokenKind::kLBrace)) ++depth;
    if (p.Check(TokenKind::kRBrace)) --depth;
    if (p.Check(TokenKind::kKwLocal)) {
      ReportLocalQualifier(p.CurrentLoc(), p.diag_);
    }
  }
  p.lexer_.RestorePos(saved);
}

void ParserConstraintItemHelpers::Capture(Parser& p, ClassMember* member) {
  if (member == nullptr) return;
  auto saved = p.lexer_.SavePos();
  const uint32_t kErrors = p.diag_.SuppressedErrorCount();
  p.diag_.PushSuppress();
  std::vector<ConstraintItem*> items;
  const bool kParsed = ParseItemsToBrace(p, items, false);
  p.diag_.PopSuppress();
  const bool kClean = p.diag_.SuppressedErrorCount() == kErrors;
  const SourceLoc kBreak =
      kClean ? p.CurrentLoc() : p.diag_.LastSuppressedErrorLoc();
  p.lexer_.RestorePos(saved);
  if (!kParsed || !kClean) {
    p.diag_.Error(kBreak, "the constraint block's items do not parse from here",
                  Subclause("A.1.10"));
    return;
  }
  member->constraint_items = std::move(items);
  member->constraint_items_parsed = true;
}

bool ParserConstraintItemHelpers::ParseItemsToBrace(
    Parser& p, std::vector<ConstraintItem*>& out, bool in_set) {
  while (!p.Match(TokenKind::kRBrace)) {
    if (p.AtEnd()) return false;
    ConstraintItem* item = in_set ? ParseSetItem(p) : ParseExpressionItem(p);
    if (item == nullptr) return false;
    out.push_back(item);
  }
  return true;
}

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
    item->kind = ConstraintItemKind::kDisableSoft;
    item->expr = p.Match(TokenKind::kKwSoft) ? ParsePrimary(p) : nullptr;
    parsed = item->expr != nullptr && p.Match(TokenKind::kSemicolon);
  } else {
    item->soft = p.Match(TokenKind::kKwSoft);
    parsed = ParseExpressionOrDist(p, *item);
  }
  return parsed ? item : nullptr;
}

ConstraintItem* ParserConstraintItemHelpers::ParseSetItem(Parser& p) {
  if (p.Check(TokenKind::kKwSolve)) return nullptr;
  return ParseExpressionItem(p);
}

bool ParserConstraintItemHelpers::ParseSet(Parser& p,
                                           std::vector<ConstraintItem*>& out) {
  if (p.Match(TokenKind::kLBrace)) return ParseItemsToBrace(p, out, true);
  ConstraintItem* item = ParseSetItem(p);
  if (item == nullptr) return false;
  out.push_back(item);
  return true;
}

bool ParserConstraintItemHelpers::ParseIfElse(Parser& p, ConstraintItem& item) {
  item.kind = ConstraintItemKind::kIfElse;
  if (!p.Match(TokenKind::kLParen)) return false;
  item.expr = p.ParseExpr();
  if (item.expr == nullptr || !p.Match(TokenKind::kRParen)) return false;
  if (!ParseSet(p, item.body)) return false;
  item.has_else = p.Match(TokenKind::kKwElse);
  return !item.has_else || ParseSet(p, item.else_body);
}

bool ParserConstraintItemHelpers::ParseForeach(Parser& p,
                                               ConstraintItem& item) {
  item.kind = ConstraintItemKind::kForeach;
  if (!p.Match(TokenKind::kLParen)) return false;
  if (!p.CheckIdentifier() && !p.Check(TokenKind::kKwThis) &&
      !p.Check(TokenKind::kKwSuper)) {
    return false;
  }
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

bool ParserConstraintItemHelpers::ParseSolveBefore(Parser& p,
                                                   ConstraintItem& item) {
  item.kind = ConstraintItemKind::kSolveBefore;
  return ParsePrimaryList(p, item.exprs) && p.Match(TokenKind::kKwBefore) &&
         ParsePrimaryList(p, item.after) && p.Match(TokenKind::kSemicolon);
}

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

Expr* ParserConstraintItemHelpers::ParsePrimary(Parser& p) {
  auto saved = p.lexer_.SavePos();
  Expr* e = p.ParseExpr();
  const Expr* name = e;
  if (e != nullptr && e->kind == ExprKind::kCall && e->args.empty() &&
      e->with_expr == nullptr) {
    name = e->lhs;
  }
  if (IsPrimaryName(name)) return e;
  p.lexer_.RestorePos(saved);
  return nullptr;
}

bool ParserConstraintItemHelpers::ParsePrimaryList(Parser& p,
                                                   std::vector<Expr*>& out) {
  do {
    Expr* primary = ParsePrimary(p);
    if (primary == nullptr) return false;
    out.push_back(primary);
  } while (p.Match(TokenKind::kComma));
  return true;
}

}  // namespace delta
