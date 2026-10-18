#include <vector>

#include "common/arena.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/parser.h"
#include "parser/parser_property_spec_internal.h"

namespace delta {

// §16.14.2: the `[lo:hi]` item of a dist_list as the range an inside
// expression holds, §11.4.13's bracketed pair; an item written about a centre,
// `[centre +/- tol]` or `[centre +%- tol]`, is the pair inside reads that
// form as, the tolerance operator marking it.
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

// §18.5.3: one dist_item of an assertion's dist_list. A default item is held
// to the rules a constraint's is, its weight given through :/ and one at most
// in the list, `defaults` counting those written so far; one breaking them is
// reported and kept, so the rest of the list is still read.
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

// §A.8.3's expression_or_dist, `expression [ dist { dist_list } ]`, in an
// assertion. §16.14.2 has a dist in an assert or cover statement be the
// inside operator over the same values, its weights ignored, and has the
// property an assume statement assumes hold the same with or without its
// biasing, the weights only selecting among the values of a free
// variable, which this tool leaves to the design; so a dist is read as the
// inside expression over its items, with the items as written beside it for
// §37.34's distribution. A `default` item stands for the values the other
// items leave out (§18.5.3), which inside holds no range for, so it is kept
// among the items alone, where the run reads it.
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
