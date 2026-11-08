#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/parser.h"
#include "parser/parser_property_spec_internal.h"

namespace delta {

static bool IsAbortToken(TokenKind k) {
  return k == TokenKind::kKwAcceptOn || k == TokenKind::kKwRejectOn ||
         k == TokenKind::kKwSyncAcceptOn || k == TokenKind::kKwSyncRejectOn;
}

static bool OpensKeywordTerm(TokenKind k) {
  return k == TokenKind::kKwIf || k == TokenKind::kKwCase ||
         k == TokenKind::kKwNexttime || k == TokenKind::kKwSNexttime ||
         k == TokenKind::kKwAlways || k == TokenKind::kKwSAlways ||
         k == TokenKind::kKwEventually || k == TokenKind::kKwSEventually ||
         IsAbortToken(k);
}

bool ParserPropertySpecHelpers::AtSpecScanEnd(Parser& p) {
  return p.Check(TokenKind::kEof) || p.Check(TokenKind::kKwEndproperty);
}

bool ParserPropertySpecHelpers::AheadOpensKeywordTerm(Parser& p) {
  auto saved = p.lexer_.SavePos();
  while (p.Check(TokenKind::kKwNot) || p.Check(TokenKind::kLParen)) {
    p.Consume();
  }
  bool opens = OpensKeywordTerm(p.CurrentToken().kind);
  p.lexer_.RestorePos(saved);
  return opens;
}

bool ParserPropertySpecHelpers::AheadHoldsRepetition(Parser& p) {
  auto scan = p.lexer_.SavePos();
  int depth = 0;
  bool found = false;
  bool bracket = false;
  while (!AtSpecScanEnd(p)) {
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

bool ParserPropertySpecHelpers::AheadHoldsSequenceOperator(Parser& p) {
  return p.Check(TokenKind::kKwFirstMatch) ||
         AheadHolds(p, TokenKind::kKwIntersect, true) ||
         AheadHolds(p, TokenKind::kKwWithin, true) ||
         AheadHolds(p, TokenKind::kKwThroughout, true);
}

Expr* ParserPropertySpecHelpers::PropertySpecPlaceholder(Arena& arena,
                                                         SourceLoc loc) {
  auto* expr = arena.Create<Expr>();
  expr->kind = ExprKind::kIdentifier;
  expr->text = "<property_spec>";
  expr->range.start = loc;
  return expr;
}

ModuleItem* ParserPropertySpecHelpers::TryParseSequenceSpec(Parser& p,
                                                            bool& strong,
                                                            bool& written,
                                                            bool term) {
  auto saved = p.lexer_.SavePos();
  bool wrapped = p.Check(TokenKind::kKwStrong) || p.Check(TokenKind::kKwWeak);
  strong = p.Check(TokenKind::kKwStrong);
  written = wrapped;
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

bool ParserPropertySpecHelpers::AheadHolds(Parser& p, TokenKind wanted,
                                           bool to_junction) {
  auto scan = p.lexer_.SavePos();
  int depth = 0;
  bool found = false;
  while (!AtSpecScanEnd(p)) {
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

bool ParserPropertySpecHelpers::OpensPropertyGroup(Parser& p) {
  auto saved = p.lexer_.SavePos();
  p.Consume();
  const bool kOpens = BodyHasPropertyJunction(p) || AheadOpensKeywordTerm(p) ||
                      p.Check(TokenKind::kAt);
  p.lexer_.RestorePos(saved);
  return kOpens;
}

PropertyExprNode* ParserPropertySpecHelpers::TryParsePropertyGroup(
    Parser& p, bool& group) {
  group = false;
  if (!p.Check(TokenKind::kLParen) || !OpensPropertyGroup(p)) return nullptr;
  p.Consume();
  group = true;
  auto* inner = ParsePropertyImplication(p);
  if (inner != nullptr && p.Match(TokenKind::kRParen)) return inner;
  return nullptr;
}

static bool IsImplicationExpr(const Expr* e) {
  return e != nullptr && e->kind == ExprKind::kBinary &&
         (e->op == TokenKind::kPipeDashGt || e->op == TokenKind::kPipeEqGt);
}

static bool IsEdgeKeyword(TokenKind k) {
  return k == TokenKind::kKwPosedge || k == TokenKind::kKwNegedge ||
         k == TokenKind::kKwEdge;
}

Expr* ParserPropertySpecHelpers::ParseWholeExpressionActual(Parser& p) {
  auto saved = p.lexer_.SavePos();
  p.diag_.PushSuppress();
  Expr* expr = p.ParseExpr();
  bool ends = expr != nullptr && !IsImplicationExpr(expr) &&
              (p.Check(TokenKind::kComma) || p.Check(TokenKind::kRParen));
  p.diag_.PopSuppress();
  if (ends) return expr;
  p.lexer_.RestorePos(saved);
  return nullptr;
}

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
  if (IsEdgeKeyword(p.CurrentToken().kind) ||
      (p.Check(TokenKind::kLParen) && p.OpensEventGroup(true))) {
    plain = false;
    return ParseEventActual(p);
  }
  if (Expr* listed = ParseListedNamesActual(p)) {
    plain = false;
    return listed;
  }
  const bool kGroup = p.Check(TokenKind::kLParen) && p.OpensEventGroup(false);
  if (!kGroup) {
    Expr* expr = ParseWholeExpressionActual(p);
    if (expr != nullptr) return expr;
  }
  plain = false;
  PropertyExprNode* tree = ParseWholeSequenceActual(p);
  if (tree == nullptr && kGroup && !OpensPropertyGroup(p)) {
    return ParseEventActual(p);
  }
  if (tree == nullptr) tree = ParsePropertyImplication(p);
  if (tree == nullptr ||
      (!p.Check(TokenKind::kComma) && !p.Check(TokenKind::kRParen))) {
    return nullptr;
  }
  Expr* holder = PropertySpecPlaceholder(p.arena_, loc);
  holder->text = "<property_actual>";
  holder->property_actual = tree;
  return holder;
}

PropertyExprNode* ParserPropertySpecHelpers::ParseWholeSequenceActual(
    Parser& p) {
  if (p.Check(TokenKind::kAt)) return nullptr;
  auto saved = p.lexer_.SavePos();
  auto* node = NewPropertyNode(p, PropertyExprNode::Kind::kSequence);
  p.diag_.PushSuppress();
  node->sequence =
      TryParseSequenceSpec(p, node->strong, node->strength_written, false);
  p.diag_.PopSuppress();
  if (node->sequence != nullptr &&
      (p.Check(TokenKind::kComma) || p.Check(TokenKind::kRParen))) {
    return node;
  }
  p.lexer_.RestorePos(saved);
  return nullptr;
}

Expr* ParserPropertySpecHelpers::ParseFormalDefault(Parser& p) {
  Token head = p.CurrentToken();
  if (head.text == "$inferred_clock" || head.text == "$inferred_disable") {
    return nullptr;
  }
  auto saved = p.lexer_.SavePos();
  p.diag_.PushSuppress();
  bool plain = true;
  Expr* actual = ParsePropertyActualArg(p, plain);
  p.diag_.PopSuppress();
  if (actual != nullptr &&
      (p.Check(TokenKind::kComma) || p.Check(TokenKind::kRParen))) {
    return actual;
  }
  p.lexer_.RestorePos(saved);
  if (IsEdgeKeyword(head.kind)) {
    p.diag_.Error(head.loc,
                  "a default actual argument opening with an edge keyword is "
                  "not an event expression",
                  Subclause("9.4.2"));
  }
  return nullptr;
}

bool ParserPropertySpecHelpers::ParseNamedActualPrefix(Parser& p, Expr* call,
                                                       bool& named) {
  const bool kAfterNamed = named;
  named = p.Match(TokenKind::kDot);
  if (!named) return !kAfterNamed;
  if (!p.Check(TokenKind::kIdentifier)) return false;
  call->arg_names.push_back(p.Consume().text);
  return p.Match(TokenKind::kLParen);
}

bool ParserPropertySpecHelpers::ParsePropertyActualList(Parser& p, Expr* call,
                                                        bool& plain) {
  if (!p.Match(TokenKind::kLParen)) return false;
  bool named = false;
  while (!p.Check(TokenKind::kRParen) && !p.AtEnd()) {
    if (!ParseNamedActualPrefix(p, call, named)) return false;
    Expr* actual = ParsePropertyActualArg(p, plain);
    if (actual == nullptr || (named && !p.Match(TokenKind::kRParen))) {
      return false;
    }
    call->args.push_back(actual);
    if (!p.Match(TokenKind::kComma)) break;
    if (named && p.Check(TokenKind::kRParen)) return false;
  }
  return p.Match(TokenKind::kRParen);
}

Expr* ParserPropertySpecHelpers::TryParsePropertyInstance(Parser& p) {
  if (!p.Check(TokenKind::kIdentifier)) return nullptr;
  auto saved = p.lexer_.SavePos();
  p.diag_.PushSuppress();
  Token name = p.Consume();
  std::string_view callee = name.text;
  if (p.Match(TokenKind::kColonColon)) {
    if (!p.Check(TokenKind::kIdentifier)) {
      p.diag_.PopSuppress();
      p.lexer_.RestorePos(saved);
      return nullptr;
    }
    Token member = p.Consume();
    callee = *p.arena_.Create<std::string>(std::string(name.text) +
                                           "::" + std::string(member.text));
  }
  auto* call = p.arena_.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = callee;
  call->text = callee;
  call->range.start = name.loc;
  bool plain = true;
  bool ok =
      p.Check(TokenKind::kLParen) && ParsePropertyActualList(p, call, plain);
  p.diag_.PopSuppress();
  if (ok && !plain) return call;
  p.lexer_.RestorePos(saved);
  return nullptr;
}

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
    if (p.AtDollarEndingRange()) {
      p.Consume();
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

PropertyExprNode* ParserPropertySpecHelpers::ParseClockedTerm(Parser& p) {
  std::vector<EventExpr> clock;
  if (p.Match(TokenKind::kLParen)) {
    clock = p.ParseEventList();
    if (!p.Match(TokenKind::kRParen)) return nullptr;
  } else {
    clock.push_back(p.ParseNamedClockingEvent());
  }
  if (clock.empty() || clock[0].signal == nullptr) return nullptr;
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
  if (Expr* instance = TryParsePropertyInstance(p)) {
    auto* node = NewPropertyNode(p, PropertyExprNode::Kind::kBoolean);
    node->boolean = instance;
    return node;
  }
  bool wrapped = p.Check(TokenKind::kKwStrong) || p.Check(TokenKind::kKwWeak);
  if (wrapped || AheadHolds(p, TokenKind::kHashHash, true) ||
      AheadHoldsRepetition(p) || AheadHoldsSequenceOperator(p)) {
    auto* node = NewPropertyNode(p, PropertyExprNode::Kind::kSequence);
    node->sequence =
        TryParseSequenceSpec(p, node->strong, node->strength_written, true);
    return node->sequence != nullptr ? node : nullptr;
  }
  auto* node = NewPropertyNode(p, PropertyExprNode::Kind::kBoolean);
  node->boolean = ParseExpressionOrDist(p);
  return node->boolean != nullptr ? node : nullptr;
}

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

PropertyExprNode* ParserPropertySpecHelpers::ParsePropertyImplication(
    Parser& p) {
  auto saved = p.lexer_.SavePos();
  auto* node = NewPropertyNode(p, PropertyExprNode::Kind::kImplication);
  bool strong = false;
  bool written = false;
  node->sequence = TryParseSequenceSpec(p, strong, written, true);
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
  auto* negated = NewPropertyNode(p, PropertyExprNode::Kind::kNot);
  negated->operands.push_back(consequent);
  node->operands.push_back(negated);
  auto* whole = NewPropertyNode(p, PropertyExprNode::Kind::kNot);
  whole->followed_by = true;
  whole->operands.push_back(node);
  return whole;
}

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

bool ParserPropertySpecHelpers::ParseSimpleSpecBody(Parser& p,
                                                    SimpleSpecBody& body) {
  if (BodyHasPropertyJunction(p) || AheadOpensKeywordTerm(p) ||
      p.Check(TokenKind::kAt)) {
    body.property = ParsePropertyImplication(p);
    return body.property != nullptr;
  }
  while (p.Match(TokenKind::kKwNot)) body.negated = !body.negated;
  body.prop = TryParsePropertyInstance(p);
  if (body.prop != nullptr) return true;
  if (!p.BodyHasTemporalOperator() && !AheadHoldsRepetition(p) &&
      !AheadHoldsSequenceOperator(p)) {
    body.prop = ParseExpressionOrDist(p);
    return body.prop != nullptr;
  }
  body.sequence =
      TryParseSequenceSpec(p, body.strong, body.strength_written, false);
  return body.sequence != nullptr;
}

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

static bool SequenceReadsStrong(const SimpleSpecBody& body,
                                StmtKind body_kind) {
  if (body.strength_written) return body.strong;
  return body_kind == StmtKind::kCoverImmediate ||
         body_kind == StmtKind::kExpect;
}

Stmt* ParserPropertySpecHelpers::MakeSimplePropertyStmt(
    Parser& p, ModuleItem* item, StmtKind body_kind,
    const SimpleSpecBody& read) {
  SimpleSpecBody body = read;
  if (body.property == nullptr && body.sequence != nullptr &&
      SequenceNamesClocks(body.sequence->seq_linear)) {
    body.strong = SequenceReadsStrong(body, body_kind);
    body.property = TreeOfSpecBody(p, body);
    body.sequence = nullptr;
    body.negated = false;
  }
  auto* stmt = p.arena_.Create<Stmt>();
  stmt->kind = body_kind;
  stmt->range.start = item->loc;
  Expr* prop = body.prop != nullptr
                   ? body.prop
                   : PropertySpecPlaceholder(p.arena_, item->loc);
  item->assert_expr = prop;
  stmt->assert_expr = prop;
  stmt->assert_sequence = body.sequence;
  stmt->assert_strong = SequenceReadsStrong(body, body_kind);
  stmt->assert_negated = body.negated;
  PropertyExprNode* property = body.property;
  if (property != nullptr && body.negated) {
    auto* whole = NewPropertyNode(p, PropertyExprNode::Kind::kNot);
    whole->operands.push_back(property);
    property = whole;
  }
  stmt->assert_property = property;
  stmt->assert_disable_iff = body.disable_iff;
  stmt->is_concurrent_clocked = true;
  return stmt;
}

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
    tree->strength_written = body.strength_written;
  }
  if (!body.negated) return tree;
  auto* whole = NewPropertyNode(p, PropertyExprNode::Kind::kNot);
  whole->operands.push_back(tree);
  return whole;
}

void ParserPropertySpecHelpers::CapturePropertyTreeBody(Parser& p,
                                                        ModuleItem* item) {
  auto saved = p.lexer_.SavePos();
  p.diag_.PushSuppress();
  std::vector<EventExpr> clock;
  std::vector<SeqLocalDecl> locals;
  bool ok = ParsePropertyLocalDecls(p, locals);
  while (ok && p.Match(TokenKind::kAt)) {
    clock.clear();
    if (p.Match(TokenKind::kLParen)) {
      clock = p.ParseEventList();
      ok = p.Match(TokenKind::kRParen);
    } else {
      clock.push_back(p.ParseNamedClockingEvent());
    }
  }
  SimpleSpecBody body;
  if (ok) ok = p.TryParseDisableIff(body.disable_iff);
  if (ok) ok = ParseSimpleSpecBody(p, body);
  if (ok) p.Match(TokenKind::kSemicolon);
  ok = ok && p.Check(TokenKind::kKwEndproperty);
  p.diag_.PopSuppress();
  p.lexer_.RestorePos(saved);
  if (!ok) return;
  item->prop_clock = std::move(clock);
  item->prop_disable_iff = body.disable_iff;
  item->prop_body_tree = TreeOfSpecBody(p, body);
  item->prop_locals = std::move(locals);
}

}  // namespace delta
