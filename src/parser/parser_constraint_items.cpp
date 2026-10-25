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

// A.1.10: a constraint_primary short of its optional `()`: a name, reached
// through '.' or '::' from another, with its selects.
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

// A.10 footnote 48 confines the `local::` qualifier to an inline constraint
// block, and a class's own constraint block is none: reports each `local` in
// the block whose items the lexer stands at, through its closing '}', and
// leaves the lexer where it found it. The block's expressions are read with
// their reports suppressed, so the qualifier is found among the tokens.
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

// A block whose items do not parse, or parse only through a suppressed
// report, is no constraint_block A.1.10 writes, and is reported where the
// parse broke off.
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

// The items of a block, or with `in_set` of a braced constraint_set, through
// its '}'.
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
    item->expr = p.Match(TokenKind::kKwSoft) ? ParsePrimary(p) : nullptr;
    parsed = item->expr != nullptr && p.Match(TokenKind::kSemicolon);
  } else {
    item->soft = p.Match(TokenKind::kKwSoft);
    parsed = ParseExpressionOrDist(p, *item);
  }
  return parsed ? item : nullptr;
}

// A.1.10: one constraint_expression of a constraint_set, which, unlike an
// item of the block, is never a solve-before; null where it does not parse.
ConstraintItem* ParserConstraintItemHelpers::ParseSetItem(Parser& p) {
  if (p.Check(TokenKind::kKwSolve)) return nullptr;
  return ParseExpressionItem(p);
}

// A.1.10: a constraint_set, a braced list of constraint expressions or one
// constraint expression alone.
bool ParserConstraintItemHelpers::ParseSet(Parser& p,
                                           std::vector<ConstraintItem*>& out) {
  if (p.Match(TokenKind::kLBrace)) return ParseItemsToBrace(p, out, true);
  ConstraintItem* item = ParseSetItem(p);
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
// variable left out keeping its place as an empty name, and the array opening
// with a name or with this or super, A.6.8's implicit_class_handle.
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
  return ParsePrimaryList(p, item.exprs) && p.Match(TokenKind::kKwBefore) &&
         ParsePrimaryList(p, item.after) && p.Match(TokenKind::kSemicolon);
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

// A.1.10: a constraint_primary, read as an expression and kept only in its
// shape, a name ending in at most an empty `()`; null otherwise, with the
// lexer back where the primary began.
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

// A.1.10: a solve_before_list, constraint_primary { , constraint_primary }.
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
