#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/parser.h"
#include "parser/parser_property_spec_internal.h"

namespace delta {

// §16.12.14: the keywords of the four abort operators.
static bool IsAbortToken(TokenKind k) {
  return k == TokenKind::kKwAcceptOn || k == TokenKind::kKwRejectOn ||
         k == TokenKind::kKwSyncAcceptOn || k == TokenKind::kKwSyncRejectOn;
}

// Whether the token opens an operand a keyword reads: if-else, a case, a
// nexttime, an always, an eventually or an abort.
static bool OpensKeywordTerm(TokenKind k) {
  return k == TokenKind::kKwIf || k == TokenKind::kKwCase ||
         k == TokenKind::kKwNexttime || k == TokenKind::kKwSNexttime ||
         k == TokenKind::kKwAlways || k == TokenKind::kKwSAlways ||
         k == TokenKind::kKwEventually || k == TokenKind::kKwSEventually ||
         IsAbortToken(k);
}

// Whether the tokens ahead, past any `not` and any opening parenthesis,
// open an operand a keyword reads, so the spec is a property of operands
// whether or not a junction joins them. The lexer is rewound.
bool ParserPropertySpecHelpers::AheadOpensKeywordTerm(Parser& p) {
  auto saved = p.lexer_.SavePos();
  while (p.Check(TokenKind::kKwNot) || p.Check(TokenKind::kLParen)) {
    p.Consume();
  }
  bool opens = OpensKeywordTerm(p.CurrentToken().kind);
  p.lexer_.RestorePos(saved);
  return opens;
}

// Whether the tokens ahead, to the closing parenthesis of the spec, the
// semicolon ending a case item or the first `or` or `and` at the spec's
// own depth, hold §16.9.2's repetition, `[*`, `[->`, `[=` or `[+`, which
// makes the operand a sequence where no `##` does. The lexer is rewound.
bool ParserPropertySpecHelpers::AheadHoldsRepetition(Parser& p) {
  auto scan = p.lexer_.SavePos();
  int depth = 0;
  bool found = false;
  bool bracket = false;
  while (!p.Check(TokenKind::kEof)) {
    TokenKind k = p.CurrentToken().kind;
    if (k == TokenKind::kLParen) {
      ++depth;
    } else if (k == TokenKind::kRParen) {
      if (depth == 0) break;
      --depth;
    } else if (depth == 0 && (k == TokenKind::kKwOr || k == TokenKind::kKwAnd ||
                              k == TokenKind::kSemicolon)) {
      break;
    } else if (bracket && (k == TokenKind::kStar || k == TokenKind::kArrow ||
                           k == TokenKind::kEq || k == TokenKind::kPlus)) {
      found = true;
      break;
    }
    bracket = k == TokenKind::kLBracket;
    p.Consume();
  }
  p.lexer_.RestorePos(scan);
  return found;
}

// §16.9.6, §16.9.8, §16.9.9 and §16.9.10: whether the tokens ahead hold a
// sequence operator no boolean has, intersect, within, throughout or
// first_match, which makes the operand a sequence where no cycle delay or
// repetition does.
bool ParserPropertySpecHelpers::AheadHoldsSequenceOperator(Parser& p) {
  return p.Check(TokenKind::kKwFirstMatch) ||
         AheadHolds(p, TokenKind::kKwIntersect, true) ||
         AheadHolds(p, TokenKind::kKwWithin, true) ||
         AheadHolds(p, TokenKind::kKwThroughout, true);
}

// The expression standing for a property_spec the assertion does not carry
// as one: a skipped spec, or a sequential property carried as a sequence.
Expr* ParserPropertySpecHelpers::PropertySpecPlaceholder(Arena& arena,
                                                         SourceLoc loc) {
  auto* expr = arena.Create<Expr>();
  expr->kind = ExprKind::kIdentifier;
  expr->text = "<property_spec>";
  expr->range.start = loc;
  return expr;
}

// §16.12.2: the sequence_expr of a sequential property, bare or under
// strong(...) or weak(...), read as a linear sequence body into a sequence
// declaration of its own; `strong` says which operator was written, and
// `term` that the sequence is one operand of a property's or or and, read
// to the operator. Answers nullptr, the lexer where it was, where the
// sequence is not one the monitor reads.
ModuleItem* ParserPropertySpecHelpers::TryParseSequenceSpec(Parser& p,
                                                            bool& strong,
                                                            bool term) {
  auto saved = p.lexer_.SavePos();
  bool wrapped = p.Check(TokenKind::kKwStrong) || p.Check(TokenKind::kKwWeak);
  strong = p.Check(TokenKind::kKwStrong);
  if (wrapped) {
    p.Consume();
    if (!p.Match(TokenKind::kLParen)) {
      p.lexer_.RestorePos(saved);
      return nullptr;
    }
  }
  auto* sequence = p.arena_.Create<ModuleItem>();
  sequence->kind = ModuleItemKind::kSequenceDecl;
  sequence->loc = p.CurrentLoc();
  bool ok = (term && !wrapped) ? p.ParseSequenceTermInto(sequence)
                               : p.ParseSequenceExprInto(sequence);
  if (ok && wrapped) ok = p.Match(TokenKind::kRParen);
  if (!ok) {
    p.lexer_.RestorePos(saved);
    return nullptr;
  }
  return sequence;
}

// Whether the tokens ahead, to the closing parenthesis of the spec, the
// semicolon ending a case item at the spec's own depth or, where
// `to_junction` says so, the first `or` or `and` at that depth, hold a
// token `wanted` at that depth or below.
bool ParserPropertySpecHelpers::AheadHolds(Parser& p, TokenKind wanted,
                                           bool to_junction) {
  auto scan = p.lexer_.SavePos();
  int depth = 0;
  bool found = false;
  while (!p.Check(TokenKind::kEof)) {
    TokenKind k = p.CurrentToken().kind;
    bool junction = k == TokenKind::kKwOr || k == TokenKind::kKwAnd;
    if (k == TokenKind::kLParen) {
      ++depth;
    } else if (k == TokenKind::kRParen) {
      if (depth == 0) break;
      --depth;
    } else if (depth == 0 &&
               (k == TokenKind::kSemicolon || (junction && to_junction))) {
      break;
    } else if (k == wanted && (depth == 0 || !junction)) {
      found = true;
      break;
    }
    p.Consume();
  }
  p.lexer_.RestorePos(scan);
  return found;
}

// Whether the spec holds an `or` or an `and` at its own depth, or an
// implication, a followed-by, implies, iff or an until, which makes it a
// property built of operands (§16.12.4, §16.12.5, §16.12.7 to §16.12.9,
// §16.12.12) rather than one operand; a
// sequence's own `or` and `and` read the same, which §16.12.2's strength rules
// make the same property.
bool ParserPropertySpecHelpers::BodyHasPropertyJunction(Parser& p) {
  return AheadHolds(p, TokenKind::kKwOr, false) ||
         AheadHolds(p, TokenKind::kKwAnd, false) ||
         AheadHolds(p, TokenKind::kPipeDashGt, false) ||
         AheadHolds(p, TokenKind::kPipeEqGt, false) ||
         AheadHolds(p, TokenKind::kHashMinusHash, false) ||
         AheadHolds(p, TokenKind::kHashEqHash, false) ||
         AheadHolds(p, TokenKind::kKwImplies, false) ||
         AheadHolds(p, TokenKind::kKwUntil, false) ||
         AheadHolds(p, TokenKind::kKwSUntil, false) ||
         AheadHolds(p, TokenKind::kKwUntilWith, false) ||
         AheadHolds(p, TokenKind::kKwSUntilWith, false) ||
         AheadHolds(p, TokenKind::kKwIff, false);
}

PropertyExprNode* ParserPropertySpecHelpers::NewPropertyNode(
    Parser& p, PropertyExprNode::Kind kind) {
  auto* node = p.arena_.Create<PropertyExprNode>();
  node->kind = kind;
  return node;
}

// A parenthesised property holding an or or an and of its own, or opening
// with an operand a keyword reads, read as one operand; `group` says the
// tokens were such a group, and the node is null where the group failed to
// read. The lexer is left where it was where the parentheses hold no such
// property.
PropertyExprNode* ParserPropertySpecHelpers::TryParsePropertyGroup(
    Parser& p, bool& group) {
  group = false;
  if (!p.Check(TokenKind::kLParen)) return nullptr;
  auto saved = p.lexer_.SavePos();
  p.Consume();
  // §16.13.2: a parenthesised operand opening with a clocking event of its
  // own, `(@(posedge clk1) sig1)`, is a property operand as well.
  if (!BodyHasPropertyJunction(p) && !AheadOpensKeywordTerm(p) &&
      !p.Check(TokenKind::kAt)) {
    p.lexer_.RestorePos(saved);
    return nullptr;
  }
  group = true;
  auto* inner = ParsePropertyImplication(p);
  if (inner != nullptr && p.Match(TokenKind::kRParen)) return inner;
  return nullptr;
}

// §16.12.7: the expression parser joins an antecedent to a consequent under
// `|->` and `|=>`, which only a sequence body's read stops at, so an actual
// read as such an expression is a property_expr, to be read as one.
static bool IsImplicationExpr(const Expr* e) {
  return e != nullptr && e->kind == ExprKind::kBinary &&
         (e->op == TokenKind::kPipeDashGt || e->op == TokenKind::kPipeEqGt);
}

// §16.12.18: one actual argument of a property instance: `$`, kept as an
// identifier named `$`; an event expression opening with an edge keyword,
// kept as the edge over its signal for a formal of type event; an
// expression running to the comma or parenthesis ending the argument; or,
// where the tokens are not one, a sequence_expr or a property_expr for a
// formal of type sequence or property, read as a property and carried by
// an identifier standing in the argument's place. `plain` is cleared where
// the argument is not an expression.
Expr* ParserPropertySpecHelpers::ParsePropertyActualArg(Parser& p,
                                                        bool& plain) {
  SourceLoc loc = p.CurrentLoc();
  if (p.Check(TokenKind::kDollar)) {
    Token tok = p.Consume();
    auto* dollar = p.arena_.Create<Expr>();
    dollar->kind = ExprKind::kIdentifier;
    dollar->text = tok.text;
    dollar->range.start = tok.loc;
    return dollar;
  }
  if (p.Check(TokenKind::kKwPosedge) || p.Check(TokenKind::kKwNegedge) ||
      p.Check(TokenKind::kKwEdge)) {
    plain = false;
    Token edge = p.Consume();
    auto* event = p.arena_.Create<Expr>();
    event->kind = ExprKind::kUnary;
    event->op = edge.kind;
    event->text = edge.text;
    event->range.start = edge.loc;
    event->lhs = p.ParseExpr();
    return event->lhs != nullptr ? event : nullptr;
  }
  auto saved = p.lexer_.SavePos();
  p.diag_.PushSuppress();
  Expr* expr = p.ParseExpr();
  bool ends = expr != nullptr && !IsImplicationExpr(expr) &&
              (p.Check(TokenKind::kComma) || p.Check(TokenKind::kRParen));
  p.diag_.PopSuppress();
  if (ends) return expr;
  p.lexer_.RestorePos(saved);
  plain = false;
  PropertyExprNode* tree = ParsePropertyImplication(p);
  if (tree == nullptr ||
      (!p.Check(TokenKind::kComma) && !p.Check(TokenKind::kRParen))) {
    return nullptr;
  }
  Expr* holder = PropertySpecPlaceholder(p.arena_, loc);
  holder->text = "<property_actual>";
  holder->property_actual = tree;
  return holder;
}

// The `.formal(` opening an actual bound by name, where one is written,
// the name recorded on `call`; `named` says one was, and the answer is
// false where it is malformed.
bool ParserPropertySpecHelpers::ParseNamedActualPrefix(Parser& p, Expr* call,
                                                       bool& named) {
  named = p.Match(TokenKind::kDot);
  if (!named) return true;
  if (!p.Check(TokenKind::kIdentifier)) return false;
  call->arg_names.push_back(p.Consume().text);
  return p.Match(TokenKind::kLParen);
}

// The `( actuals )` of a property instance into `call`, each actual bound
// by position or, as `.formal(actual)`, by name; false where the list is
// malformed.
bool ParserPropertySpecHelpers::ParsePropertyActualList(Parser& p, Expr* call,
                                                        bool& plain) {
  if (!p.Match(TokenKind::kLParen)) return false;
  while (!p.Check(TokenKind::kRParen) && !p.AtEnd()) {
    bool named = false;
    if (!ParseNamedActualPrefix(p, call, named)) return false;
    Expr* actual = ParsePropertyActualArg(p, plain);
    if (actual == nullptr || (named && !p.Match(TokenKind::kRParen))) {
      return false;
    }
    call->args.push_back(actual);
    if (!p.Match(TokenKind::kComma)) break;
  }
  return p.Match(TokenKind::kRParen);
}

// §16.12.1 and §16.12.18: `name ( actuals )` where an actual is a
// sequence_expr, a property_expr or an event expression, which no
// expression holds, read as an instance of a named property. The lexer is
// left where it was, and nullptr answered, where the tokens are not that,
// an instance whose actuals are all expressions included, which reads as a
// call does.
Expr* ParserPropertySpecHelpers::TryParsePropertyInstance(Parser& p) {
  if (!p.Check(TokenKind::kIdentifier)) return nullptr;
  auto saved = p.lexer_.SavePos();
  p.diag_.PushSuppress();
  Token name = p.Consume();
  auto* call = p.arena_.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = name.text;
  call->text = name.text;
  call->range.start = name.loc;
  bool plain = true;
  bool ok =
      p.Check(TokenKind::kLParen) && ParsePropertyActualList(p, call, plain);
  p.diag_.PopSuppress();
  if (ok && !plain) return call;
  p.lexer_.RestorePos(saved);
  return nullptr;
}

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

// §A.8.3's expression_or_dist, `expression [ dist { dist_list } ]`, in an
// assertion. §16.14.2 has a dist in an assert or cover statement be the
// inside operator over the same values, its weights ignored, and has the
// property an assume statement assumes hold the same with or without its
// biasing, the weights only selecting among the values of a free
// variable, which this tool leaves to the design; so a dist is read as the
// inside expression over its items. A `default` item weights the values
// the other items leave out, which inside holds no range for, so a
// dist_list writing one is not read.
Expr* ParserPropertySpecHelpers::ParseExpressionOrDist(Parser& p) {
  Expr* expr = p.ParseExpr();
  if (expr == nullptr || !p.Check(TokenKind::kKwDist)) return expr;
  p.Consume();
  if (!p.Match(TokenKind::kLBrace)) return nullptr;
  auto* inside = p.arena_.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->range.start = expr->range.start;
  inside->lhs = expr;
  do {
    ConstraintDistItem item;
    if (!p.ParseDistItem(item) || item.is_default) return nullptr;
    inside->elements.push_back(item.is_range ? RangeOfDistItem(p, item)
                                             : item.value);
  } while (p.Match(TokenKind::kComma));
  return p.Match(TokenKind::kRBrace) ? inside : nullptr;
}

// §16.12.6: `if ( expression_or_dist ) property_expr [ else property_expr
// ]`, the if keyword consumed; Table 16-3 puts if-else below every other
// operator, so each branch runs to the else or the end.
PropertyExprNode* ParserPropertySpecHelpers::ParsePropertyIfElse(Parser& p) {
  auto* node = NewPropertyNode(p, PropertyExprNode::Kind::kIfElse);
  if (!p.Match(TokenKind::kLParen)) return nullptr;
  node->boolean = ParseExpressionOrDist(p);
  if (node->boolean == nullptr || !p.Match(TokenKind::kRParen)) {
    return nullptr;
  }
  auto* then_branch = ParsePropertyImplication(p);
  if (then_branch == nullptr) return nullptr;
  node->operands.push_back(then_branch);
  if (p.Match(TokenKind::kKwElse)) {
    auto* else_branch = ParsePropertyImplication(p);
    if (else_branch == nullptr) return nullptr;
    node->operands.push_back(else_branch);
  }
  return node;
}

// §16.12.16: one property_case_item, `expression_or_dist { ,
// expression_or_dist } : property_expr ;` or `default [ : ] property_expr
// ;`, its expressions and its property added to `node`, the default's
// expressions none. Answers false where the item failed to read.
bool ParserPropertySpecHelpers::ParsePropertyCaseItem(Parser& p,
                                                      PropertyExprNode& node) {
  std::vector<Expr*> values;
  if (p.Match(TokenKind::kKwDefault)) {
    p.Match(TokenKind::kColon);
  } else {
    do {
      Expr* value = p.ParseExpr();
      if (value == nullptr) return false;
      values.push_back(value);
    } while (p.Match(TokenKind::kComma));
    if (!p.Match(TokenKind::kColon)) return false;
  }
  auto* property = ParsePropertyImplication(p);
  if (property == nullptr || !p.Match(TokenKind::kSemicolon)) return false;
  node.case_values.push_back(std::move(values));
  node.operands.push_back(property);
  return true;
}

// §16.12.16: `case ( expression_or_dist ) property_case_item {
// property_case_item } endcase`, the case keyword consumed; Table 16-3
// puts case beside if-else, below every other operator, so each item's
// property runs to its semicolon.
PropertyExprNode* ParserPropertySpecHelpers::ParsePropertyCase(Parser& p) {
  auto* node = NewPropertyNode(p, PropertyExprNode::Kind::kCase);
  if (!p.Match(TokenKind::kLParen)) return nullptr;
  node->boolean = ParseExpressionOrDist(p);
  if (node->boolean == nullptr || !p.Match(TokenKind::kRParen)) {
    return nullptr;
  }
  while (!p.Match(TokenKind::kKwEndcase)) {
    if (p.Check(TokenKind::kEof) || !ParsePropertyCaseItem(p, *node)) {
      return nullptr;
    }
  }
  return node->operands.empty() ? nullptr : node;
}

// One operand of a property's or or and: `not` before an operand negates
// it (§16.12.3); an if-else is read whole (§16.12.6); a parenthesised
// property holding an or or and of its own is read as one; and otherwise
// the operand is a sequence where it holds a cycle delay before the next
// operator or stands under strong or weak, and a boolean else.
// §16.12.10: `nexttime [ [ constant_expression ] ] property_expr` and the
// strong s_nexttime, the operand bound as tightly as not's.
PropertyExprNode* ParserPropertySpecHelpers::ParsePropertyNexttime(
    Parser& p, bool strong) {
  auto* node = NewPropertyNode(p, PropertyExprNode::Kind::kNexttime);
  node->strong = strong;
  if (p.Match(TokenKind::kLBracket)) {
    node->boolean = p.ParseExpr();
    if (node->boolean == nullptr || !p.Match(TokenKind::kRBracket)) {
      return nullptr;
    }
  }
  auto* operand = ParsePropertyTerm(p);
  if (operand == nullptr) return nullptr;
  node->operands.push_back(operand);
  return node;
}

// §16.12.11 and §16.12.13: `always [ [ range ] ] property_expr`, `s_always
// [ range ] property_expr`, `eventually [ range ] property_expr` and
// `s_eventually [ [ range ] ] property_expr`, the range `min:max` or
// `min:$`, the operand any property as Table 16-3 puts both beside if-else,
// below every other operator.
PropertyExprNode* ParserPropertySpecHelpers::ParsePropertyAlways(
    Parser& p, PropertyExprNode::Kind kind, bool strong) {
  auto* node = NewPropertyNode(p, kind);
  node->strong = strong;
  node->range_unbounded = true;
  if (p.Match(TokenKind::kLBracket)) {
    node->range_min = p.ParseExpr();
    if (node->range_min == nullptr || !p.Match(TokenKind::kColon)) {
      return nullptr;
    }
    if (p.Match(TokenKind::kDollar)) {
      node->range_unbounded = true;
    } else {
      node->range_max = p.ParseExpr();
      node->range_unbounded = false;
      if (node->range_max == nullptr) return nullptr;
    }
    if (!p.Match(TokenKind::kRBracket)) return nullptr;
  }
  auto* operand = ParsePropertyImplication(p);
  if (operand == nullptr) return nullptr;
  node->operands.push_back(operand);
  return node;
}

// The operators that open an operand with a keyword: if-else, case, always
// and eventually in their weak and strong forms, nexttime likewise and not;
// `read` says the keyword was one of them, and the node is null where its
// operand failed to read.
PropertyExprNode* ParserPropertySpecHelpers::TryParseKeywordTerm(Parser& p,
                                                                 bool& read) {
  read = true;
  if (p.Match(TokenKind::kKwIf)) return ParsePropertyIfElse(p);
  if (p.Match(TokenKind::kKwCase)) return ParsePropertyCase(p);
  if (p.Match(TokenKind::kKwAlways)) {
    return ParsePropertyAlways(p, PropertyExprNode::Kind::kAlways, false);
  }
  if (p.Match(TokenKind::kKwSAlways)) {
    return ParsePropertyAlways(p, PropertyExprNode::Kind::kAlways, true);
  }
  if (p.Match(TokenKind::kKwEventually)) {
    return ParsePropertyAlways(p, PropertyExprNode::Kind::kEventually, false);
  }
  if (p.Match(TokenKind::kKwSEventually)) {
    return ParsePropertyAlways(p, PropertyExprNode::Kind::kEventually, true);
  }
  if (p.Match(TokenKind::kKwNexttime)) return ParsePropertyNexttime(p, false);
  if (p.Match(TokenKind::kKwSNexttime)) return ParsePropertyNexttime(p, true);
  if (IsAbortToken(p.CurrentToken().kind)) return ParsePropertyAbort(p);
  if (p.Match(TokenKind::kKwNot)) {
    auto* node = NewPropertyNode(p, PropertyExprNode::Kind::kNot);
    auto* operand = ParsePropertyTerm(p);
    if (operand == nullptr) return nullptr;
    node->operands.push_back(operand);
    return node;
  }
  read = false;
  return nullptr;
}

// §16.12.14: `accept_on ( expression_or_dist ) property_expr`, reject_on
// and the sync_ forms, the operand any property as Table 16-3 puts the
// aborts beside if-else, below every other operator.
PropertyExprNode* ParserPropertySpecHelpers::ParsePropertyAbort(Parser& p) {
  TokenKind op = p.Consume().kind;
  auto* node = NewPropertyNode(p, PropertyExprNode::Kind::kAbort);
  node->accept =
      op == TokenKind::kKwAcceptOn || op == TokenKind::kKwSyncAcceptOn;
  node->synchronous =
      op == TokenKind::kKwSyncAcceptOn || op == TokenKind::kKwSyncRejectOn;
  if (!p.Match(TokenKind::kLParen)) return nullptr;
  node->boolean = ParseExpressionOrDist(p);
  if (node->boolean == nullptr || !p.Match(TokenKind::kRParen)) {
    return nullptr;
  }
  auto* operand = ParsePropertyImplication(p);
  if (operand == nullptr) return nullptr;
  node->operands.push_back(operand);
  return node;
}

// §16.13.2: `@(event_list)` before an operand, the clock the operand is
// evaluated on from its nearest tick; the operand it reads is the term
// after it, a sequence with the clock on its operands where the term is
// one.
PropertyExprNode* ParserPropertySpecHelpers::ParseClockedTerm(Parser& p) {
  if (!p.Match(TokenKind::kLParen)) return nullptr;
  std::vector<EventExpr> clock = p.ParseEventList();
  if (!p.Match(TokenKind::kRParen) || clock.empty()) return nullptr;
  auto* operand = ParsePropertyTerm(p);
  if (operand != nullptr && operand->clock.empty()) operand->clock = clock;
  return operand;
}

PropertyExprNode* ParserPropertySpecHelpers::ParsePropertyTerm(Parser& p) {
  if (p.Match(TokenKind::kAt)) return ParseClockedTerm(p);
  bool read = false;
  auto* keyword = TryParseKeywordTerm(p, read);
  if (read) return keyword;
  bool group = false;
  auto* inner = TryParsePropertyGroup(p, group);
  if (group) return inner;
  // §16.12.18: an instance whose actuals hold a sequence or a property is
  // read before the scans below, which its actuals would answer.
  if (Expr* instance = TryParsePropertyInstance(p)) {
    auto* node = NewPropertyNode(p, PropertyExprNode::Kind::kBoolean);
    node->boolean = instance;
    return node;
  }
  bool wrapped = p.Check(TokenKind::kKwStrong) || p.Check(TokenKind::kKwWeak);
  if (wrapped || AheadHolds(p, TokenKind::kHashHash, true) ||
      AheadHoldsRepetition(p) || AheadHoldsSequenceOperator(p)) {
    auto* node = NewPropertyNode(p, PropertyExprNode::Kind::kSequence);
    node->sequence = TryParseSequenceSpec(p, node->strong, true);
    return node->sequence != nullptr ? node : nullptr;
  }
  auto* node = NewPropertyNode(p, PropertyExprNode::Kind::kBoolean);
  node->boolean = ParseExpressionOrDist(p);
  return node->boolean != nullptr ? node : nullptr;
}

// §16.12.5 and Table 16-3: `and` binds tighter than `or`, both left
// associative, so an `and` gathers its operands under one node and an
// `or` gathers the conjunctions.
PropertyExprNode* ParserPropertySpecHelpers::ParsePropertyAnd(Parser& p) {
  auto* left = ParsePropertyTerm(p);
  if (left == nullptr || !p.Check(TokenKind::kKwAnd)) return left;
  auto* node = NewPropertyNode(p, PropertyExprNode::Kind::kAnd);
  node->operands.push_back(left);
  while (p.Match(TokenKind::kKwAnd)) {
    auto* right = ParsePropertyTerm(p);
    if (right == nullptr) return nullptr;
    node->operands.push_back(right);
  }
  return node;
}

// §16.12.7 and §16.12.9: `sequence_expr |-> property_expr`, `|=>`, `#-#`
// and `#=#`, the antecedent a sequence read to the operator and the
// consequent any property, the operators right associative and, in Table
// 16-3, above if-else alone; a spec without one is its implies.
PropertyExprNode* ParserPropertySpecHelpers::ParsePropertyImplication(
    Parser& p) {
  auto saved = p.lexer_.SavePos();
  auto* node = NewPropertyNode(p, PropertyExprNode::Kind::kImplication);
  bool strong = false;
  node->sequence = TryParseSequenceSpec(p, strong, true);
  TokenKind op = p.CurrentToken().kind;
  bool implication = op == TokenKind::kPipeDashGt || op == TokenKind::kPipeEqGt;
  bool followed_by =
      op == TokenKind::kHashMinusHash || op == TokenKind::kHashEqHash;
  if (node->sequence == nullptr || strong || (!implication && !followed_by)) {
    p.lexer_.RestorePos(saved);
    return ParsePropertyImplies(p);
  }
  p.Consume();
  node->strong = op == TokenKind::kPipeEqGt || op == TokenKind::kHashEqHash;
  auto* consequent = ParsePropertyImplication(p);
  if (consequent == nullptr) return nullptr;
  if (!followed_by) {
    node->operands.push_back(consequent);
    return node;
  }
  // §16.12.9: `s #-# p` is `not (s |-> not p)` and `s #=# p` is `not (s
  // |=> not p)`, the followed-bys being the duals of the implications.
  auto* negated = NewPropertyNode(p, PropertyExprNode::Kind::kNot);
  negated->operands.push_back(consequent);
  node->operands.push_back(negated);
  auto* whole = NewPropertyNode(p, PropertyExprNode::Kind::kNot);
  whole->operands.push_back(node);
  return whole;
}

// §16.12.8 and Table 16-3: `iff` binds tighter than `implies` and looser
// than `or`, both right associative, each over two operands.
PropertyExprNode* ParserPropertySpecHelpers::ParsePropertyIff(Parser& p) {
  auto* left = ParsePropertyOr(p);
  if (left == nullptr || !p.Match(TokenKind::kKwIff)) return left;
  auto* node = NewPropertyNode(p, PropertyExprNode::Kind::kIff);
  node->operands.push_back(left);
  auto* right = ParsePropertyIff(p);
  if (right == nullptr) return nullptr;
  node->operands.push_back(right);
  return node;
}

// §16.12.8 and §16.12.12: `implies` and the four untils stand in one row of
// Table 16-3, right associative, below iff; an until is strong where it is
// s_until or s_until_with and overlapping where it is until_with or
// s_until_with.
PropertyExprNode* ParserPropertySpecHelpers::ParsePropertyImplies(Parser& p) {
  auto* left = ParsePropertyIff(p);
  if (left == nullptr) return nullptr;
  TokenKind op = p.CurrentToken().kind;
  bool until = op == TokenKind::kKwUntil || op == TokenKind::kKwSUntil ||
               op == TokenKind::kKwUntilWith || op == TokenKind::kKwSUntilWith;
  if (op != TokenKind::kKwImplies && !until) return left;
  p.Consume();
  auto* node = NewPropertyNode(p, until ? PropertyExprNode::Kind::kUntil
                                        : PropertyExprNode::Kind::kImplies);
  node->strong = op == TokenKind::kKwSUntil || op == TokenKind::kKwSUntilWith;
  node->range_unbounded =
      op == TokenKind::kKwUntilWith || op == TokenKind::kKwSUntilWith;
  node->operands.push_back(left);
  auto* right = ParsePropertyImplies(p);
  if (right == nullptr) return nullptr;
  node->operands.push_back(right);
  return node;
}

PropertyExprNode* ParserPropertySpecHelpers::ParsePropertyOr(Parser& p) {
  auto* left = ParsePropertyAnd(p);
  if (left == nullptr || !p.Check(TokenKind::kKwOr)) return left;
  auto* node = NewPropertyNode(p, PropertyExprNode::Kind::kOr);
  node->operands.push_back(left);
  while (p.Match(TokenKind::kKwOr)) {
    auto* right = ParsePropertyAnd(p);
    if (right == nullptr) return nullptr;
    node->operands.push_back(right);
  }
  return node;
}

// §16.12.2: the body of the spec after its clock and disable condition: a
// spec holding an or or an and at its own depth is a property of operands
// read as a tree into `property`; one holding `##` and no property
// operator is a sequential property, read as a sequence into `sequence`;
// one holding neither a cycle delay nor an implication is a boolean, read
// into `prop`. Answers false where the body is none of these.
bool ParserPropertySpecHelpers::ParseSimpleSpecBody(Parser& p,
                                                    SimpleSpecBody& body) {
  // Table 16-3 has `not` bind tighter than `or` and `and`, so where the
  // spec is a property of operands a leading `not` is the first operand's,
  // read with the operands; a spec opening with an operand a keyword reads,
  // after any nots and parentheses, is a property of operands as well, as
  // is one opening with a clocking event, §16.14.1's `abc` writing its
  // clock after its disable condition, where §A.2.10 has the property_expr
  // begin.
  if (BodyHasPropertyJunction(p) || AheadOpensKeywordTerm(p) ||
      p.Check(TokenKind::kAt)) {
    body.property = ParsePropertyImplication(p);
    return body.property != nullptr;
  }
  // §16.12.3: each `not` before the body negates it once more.
  while (p.Match(TokenKind::kKwNot)) body.negated = !body.negated;
  // §16.12.18: an instance whose actuals hold a sequence or a property is
  // read before the scan below, which its actuals would answer.
  body.prop = TryParsePropertyInstance(p);
  if (body.prop != nullptr) return true;
  // §16.9.2: a repetition makes the spec a sequence where no cycle delay
  // does, `a[*0:2]` as much as `a ##1 b`.
  if (!p.BodyHasTemporalOperator() && !AheadHoldsRepetition(p) &&
      !AheadHoldsSequenceOperator(p)) {
    body.prop = ParseExpressionOrDist(p);
    return body.prop != nullptr;
  }
  body.sequence = TryParseSequenceSpec(p, body.strong, false);
  return body.sequence != nullptr;
}

// The statement carrying the property_spec read, for the process the
// elaborator makes of the assertion: its clock is the item's sensitivity,
// and a `not` before a property of operands negates the whole.
// §16.13.1: whether the body, or an operand of its intersect, and or or,
// names a clock of its own.
static bool SequenceNamesClocks(const SeqLinearBody& body) {
  for (const auto& clock : body.clocks) {
    if (!clock.empty()) return true;
  }
  for (const SeqLinearBody& inner : body.intersects) {
    if (SequenceNamesClocks(inner)) return true;
  }
  for (const SeqLinearBody& inner : body.conjuncts) {
    if (SequenceNamesClocks(inner)) return true;
  }
  for (const SeqLinearBody& inner : body.alternatives) {
    if (SequenceNamesClocks(inner)) return true;
  }
  return false;
}

// §16.12.2 and F.4.1: the statements whose bare sequence is read as
// strong(...), a cover and an expect.
static bool BareSequenceIsStrong(StmtKind body_kind) {
  return body_kind == StmtKind::kCoverImmediate ||
         body_kind == StmtKind::kExpect;
}

Stmt* ParserPropertySpecHelpers::MakeSimplePropertyStmt(
    Parser& p, ModuleItem* item, StmtKind body_kind,
    const SimpleSpecBody& read) {
  // §16.13.1: a sequence whose operands name clocks of their own is
  // evaluated as a tree of one operand, where the ticks of each clock are
  // told apart.
  SimpleSpecBody body = read;
  if (body.property == nullptr && body.sequence != nullptr &&
      SequenceNamesClocks(body.sequence->seq_linear)) {
    body.strong = body.strong || BareSequenceIsStrong(body_kind);
    body.property = TreeOfSpecBody(p, body);
    body.sequence = nullptr;
    body.negated = false;
  }
  auto* stmt = p.arena_.Create<Stmt>();
  stmt->kind = body_kind;
  stmt->range.start = item->loc;
  // A sequential property or a property of operands stands under the
  // placeholder a skipped spec does, so what reads the item's expression
  // finds one; the evaluation reads the sequence or the tree.
  Expr* prop = body.prop != nullptr
                   ? body.prop
                   : PropertySpecPlaceholder(p.arena_, item->loc);
  item->assert_expr = prop;
  stmt->assert_expr = prop;
  stmt->assert_sequence = body.sequence;
  // §16.12.2: a sequence_expr in an assert or assume is evaluated as weak
  // unless written strong(...), and one in a cover as strong, F.4.1 having
  // an expect statement's read as a cover's.
  stmt->assert_strong = body.strong || BareSequenceIsStrong(body_kind);
  stmt->assert_negated = body.negated;
  PropertyExprNode* property = body.property;
  if (property != nullptr && body.negated) {
    auto* whole = NewPropertyNode(p, PropertyExprNode::Kind::kNot);
    whole->operands.push_back(property);
    property = whole;
  }
  stmt->assert_property = property;
  stmt->assert_disable_iff = body.disable_iff;
  // §16.5: this statement carries a concurrent assertion's property, not
  // an immediate assertion's expression, so the mark travels with it to
  // the evaluation that §16.5.1 gives sampled values.
  stmt->is_concurrent_clocked = true;
  return stmt;
}

// The body as one tree: the tree read, or a node over the boolean or the
// sequence with its strength, under a not where the body was negated.
PropertyExprNode* ParserPropertySpecHelpers::TreeOfSpecBody(
    Parser& p, const SimpleSpecBody& body) {
  PropertyExprNode* tree = body.property;
  if (tree == nullptr) {
    tree = NewPropertyNode(p, body.sequence != nullptr
                                  ? PropertyExprNode::Kind::kSequence
                                  : PropertyExprNode::Kind::kBoolean);
    tree->boolean = body.prop;
    tree->sequence = body.sequence;
    tree->strong = body.strong;
  }
  if (!body.negated) return tree;
  auto* whole = NewPropertyNode(p, PropertyExprNode::Kind::kNot);
  whole->operands.push_back(tree);
  return whole;
}

// §16.12 and §16.12.17: the body of a named property declaration,
// trial-parsed as an assertion's property_spec is -- the local variables
// declared ahead of it (§16.10), a clock where one is written, a disable
// condition where one is, and the property -- and recorded in
// prop_body_tree with the locals, the clock and the condition beside, so
// that an instance of the property, in an assertion or in a property's
// body, its own included, is evaluated as the body with the actuals
// substituted. The clocked boolean form is captured as a tree too, a
// boolean under a not where negated, for the instance whose actuals the
// boolean substitution does not read (§16.12.18). Diagnostics are
// suppressed and the lexer rewound, so the body scan re-reads the same
// tokens; a body of any other shape leaves the tree null.
void ParserPropertySpecHelpers::CapturePropertyTreeBody(Parser& p,
                                                        ModuleItem* item) {
  auto saved = p.lexer_.SavePos();
  p.diag_.PushSuppress();
  std::vector<EventExpr> clock;
  // §16.10: the body's local variables are declared ahead of the property.
  std::vector<SeqLocalDecl> locals;
  bool ok = ParsePropertyLocalDecls(p, locals);
  // §16.13.3: of two clocking events juxtaposed the second nullifies the
  // first, so the last written is the body's; §16.13 writes the event as a
  // parenthesized list or, `@clk`, as one identifier, a formal's among them.
  while (ok && p.Match(TokenKind::kAt)) {
    clock.clear();
    if (p.Match(TokenKind::kLParen)) {
      clock = p.ParseEventList();
      ok = p.Match(TokenKind::kRParen);
    } else {
      clock.push_back(p.ParseSingleEvent());
    }
  }
  SimpleSpecBody body;
  if (ok) ok = p.TryParseDisableIff(body.disable_iff);
  if (ok) ok = ParseSimpleSpecBody(p, body);
  ok = ok && p.Match(TokenKind::kSemicolon) &&
       p.Check(TokenKind::kKwEndproperty);
  p.diag_.PopSuppress();
  p.lexer_.RestorePos(saved);
  if (!ok) return;
  item->prop_clock = std::move(clock);
  item->prop_disable_iff = body.disable_iff;
  item->prop_body_tree = TreeOfSpecBody(p, body);
  item->prop_locals = std::move(locals);
}

}  // namespace delta
