#include "common/arena.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "parser/parser.h"
#include "parser/parser_property_spec_internal.h"

namespace delta {

// §16.12: the tokens of the property operators the evaluation does not read;
// not, or, and, if-else, the implications, the followed-bys, implies, iff,
// nexttime, always, the untils and eventually are read.
static bool IsPropertyOperatorToken(TokenKind k) {
  switch (k) {
    case TokenKind::kKwAcceptOn:
    case TokenKind::kKwRejectOn:
    case TokenKind::kKwSyncAcceptOn:
    case TokenKind::kKwSyncRejectOn:
    case TokenKind::kKwCase:
      return true;
    default:
      return false;
  }
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

// §16.12: whether the property_spec ahead, to its closing parenthesis,
// holds a property operator -- an implication or followed-by, a property
// keyword such as not, until or nexttime, or an if or case -- which makes
// it a property_expr and not the sequence_expr of a sequential property.
bool ParserPropertySpecHelpers::BodyHasPropertyOperator(Parser& p) {
  auto scan = p.lexer_.SavePos();
  int depth = 0;
  bool found = false;
  while (!p.Check(TokenKind::kEof)) {
    TokenKind k = p.CurrentToken().kind;
    if (k == TokenKind::kLParen) {
      ++depth;
    } else if (k == TokenKind::kRParen) {
      if (depth == 0) break;
      --depth;
    } else if (IsPropertyOperatorToken(k)) {
      found = true;
      break;
    }
    p.Consume();
  }
  p.lexer_.RestorePos(scan);
  return found;
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

// Whether the tokens ahead, to the closing parenthesis of the spec or,
// where `to_junction` says so, to the first `or` or `and` at the spec's
// own depth, hold a token `wanted` at that depth or below.
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
    } else if (depth == 0 && junction && to_junction) {
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

// A parenthesised property holding an or or an and of its own, read as
// one operand; `group` says the tokens were such a group, and the node is
// null where the group failed to read. The lexer is left where it was
// where the parentheses hold no such property.
PropertyExprNode* ParserPropertySpecHelpers::TryParsePropertyGroup(
    Parser& p, bool& group) {
  group = false;
  if (!p.Check(TokenKind::kLParen)) return nullptr;
  auto saved = p.lexer_.SavePos();
  p.Consume();
  if (!BodyHasPropertyJunction(p)) {
    p.lexer_.RestorePos(saved);
    return nullptr;
  }
  group = true;
  auto* inner = ParsePropertyImplication(p);
  if (inner != nullptr && p.Match(TokenKind::kRParen)) return inner;
  return nullptr;
}

// §16.12.6: `if ( expression_or_dist ) property_expr [ else property_expr
// ]`, the if keyword consumed; Table 16-3 puts if-else below every other
// operator, so each branch runs to the else or the end.
PropertyExprNode* ParserPropertySpecHelpers::ParsePropertyIfElse(Parser& p) {
  auto* node = NewPropertyNode(p, PropertyExprNode::Kind::kIfElse);
  if (!p.Match(TokenKind::kLParen)) return nullptr;
  node->boolean = p.ParseExpr();
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

// The operators that open an operand with a keyword: if-else, always and
// eventually in their weak and strong forms, nexttime likewise and not;
// `read` says the keyword was one of them, and the node is null where its
// operand failed to read.
PropertyExprNode* ParserPropertySpecHelpers::TryParseKeywordTerm(Parser& p,
                                                                 bool& read) {
  read = true;
  if (p.Match(TokenKind::kKwIf)) return ParsePropertyIfElse(p);
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

PropertyExprNode* ParserPropertySpecHelpers::ParsePropertyTerm(Parser& p) {
  bool read = false;
  auto* keyword = TryParseKeywordTerm(p, read);
  if (read) return keyword;
  bool group = false;
  auto* inner = TryParsePropertyGroup(p, group);
  if (group) return inner;
  bool wrapped = p.Check(TokenKind::kKwStrong) || p.Check(TokenKind::kKwWeak);
  if (wrapped || AheadHolds(p, TokenKind::kHashHash, true)) {
    auto* node = NewPropertyNode(p, PropertyExprNode::Kind::kSequence);
    node->sequence = TryParseSequenceSpec(p, node->strong, true);
    return node->sequence != nullptr ? node : nullptr;
  }
  auto* node = NewPropertyNode(p, PropertyExprNode::Kind::kBoolean);
  node->boolean = p.ParseExpr();
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
  if (BodyHasPropertyOperator(p)) return false;
  // Table 16-3 has `not` bind tighter than `or` and `and`, so where the
  // spec is a property of operands a leading `not` is the first operand's,
  // read with the operands; a spec opening with `if` is a property of
  // operands as well.
  if (BodyHasPropertyJunction(p) || p.Check(TokenKind::kKwIf) ||
      p.Check(TokenKind::kKwNexttime) || p.Check(TokenKind::kKwSNexttime) ||
      p.Check(TokenKind::kKwAlways) || p.Check(TokenKind::kKwSAlways) ||
      p.Check(TokenKind::kKwEventually) || p.Check(TokenKind::kKwSEventually)) {
    body.property = ParsePropertyImplication(p);
    return body.property != nullptr;
  }
  // §16.12.3: each `not` before the body negates it once more.
  while (p.Match(TokenKind::kKwNot)) body.negated = !body.negated;
  if (!p.BodyHasTemporalOperator()) {
    body.prop = p.ParseExpr();
    return body.prop != nullptr;
  }
  body.sequence = TryParseSequenceSpec(p, body.strong, false);
  return body.sequence != nullptr;
}

// The statement carrying the property_spec read, for the process the
// elaborator makes of the assertion: its clock is the item's sensitivity,
// and a `not` before a property of operands negates the whole.
Stmt* ParserPropertySpecHelpers::MakeSimplePropertyStmt(
    Parser& p, ModuleItem* item, StmtKind body_kind,
    const SimpleSpecBody& body) {
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
  // unless written strong(...), and one in a cover as strong.
  stmt->assert_strong = body.strong || body_kind == StmtKind::kCoverImmediate;
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

}  // namespace delta
