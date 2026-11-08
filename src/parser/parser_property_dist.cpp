#include <vector>

#include "common/arena.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/parser.h"
#include "parser/parser_property_spec_internal.h"

namespace delta {

Expr* ParserPropertySpecHelpers::RangeOfDistItem(
    Parser& p, const ConstraintDistItem& item) {
  auto* range = p.arena_.Create<Expr>();
  range->kind = ExprKind::kSelect;
  range->range.start = item.lo->range.start;
  range->index = item.lo;
  if (item.tolerance != nullptr) {
    range->op = item.tolerance_relative ? TokenKind::kPlusPercentMinus
                                        : TokenKind::kPlusSlashMinus;
    range->index_end = item.tolerance;
    return range;
  }
  range->index_end = item.hi;
  return range;
}

bool ParserPropertySpecHelpers::ParseAssertionDistItem(Parser& p,
                                                       ConstraintDistItem& item,
                                                       int& defaults) {
  if (!p.Check(TokenKind::kKwDefault)) return p.ParseDistItem(item);
  const SourceLoc kLoc = p.Consume().loc;
  item.is_default = true;
  if (p.CheckDistDefault(kLoc, defaults)) return p.ParseDistWeight(item);
  p.ParseDistWeight(item);
  return true;
}

void ParserPropertySpecHelpers::CheckDistListDefaults(Parser& p) {
  p.Consume();
  int depth = 1;
  int defaults = 0;
  while (depth > 0) {
    const Token kToken = p.Consume();
    if (kToken.kind == TokenKind::kLBrace) {
      ++depth;
    } else if (kToken.kind == TokenKind::kRBrace) {
      --depth;
    } else if (kToken.kind == TokenKind::kKwDefault) {
      p.CheckDistDefault(kToken.loc, defaults);
    }
  }
}

void ParserPropertySpecHelpers::CheckSpecDistDefaults(Parser& p) {
  int parens = 0;
  while (!p.Check(TokenKind::kRParen) || parens > 0) {
    const TokenKind kKind = p.Consume().kind;
    if (kKind == TokenKind::kLParen) {
      ++parens;
    } else if (kKind == TokenKind::kRParen) {
      --parens;
    } else if (kKind == TokenKind::kKwDist) {
      CheckDistListDefaults(p);
    }
  }
}

Expr* ParserPropertySpecHelpers::ParseExpressionOrDist(Parser& p) {
  Expr* expr = p.ParseExpr();
  if (expr == nullptr || !p.Check(TokenKind::kKwDist)) return expr;
  p.Consume();
  if (!p.Match(TokenKind::kLBrace)) return nullptr;
  auto* inside = p.arena_.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->range.start = expr->range.start;
  inside->lhs = expr;
  auto* items = p.arena_.Create<std::vector<ConstraintDistItem>>();
  inside->dist_items = items;
  int defaults = 0;
  do {
    ConstraintDistItem item;
    if (!ParseAssertionDistItem(p, item, defaults)) return nullptr;
    if (!item.is_default) {
      inside->elements.push_back(item.is_range ? RangeOfDistItem(p, item)
                                               : item.value);
    }
    items->push_back(item);
  } while (p.Match(TokenKind::kComma));
  return p.Match(TokenKind::kRBrace) ? inside : nullptr;
}

}  // namespace delta
