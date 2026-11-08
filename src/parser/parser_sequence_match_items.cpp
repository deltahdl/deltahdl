#include <vector>

#include "common/arena.h"
#include "lexer/lexer.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/parser.h"
#include "parser/parser_property_spec_internal.h"
#include "parser/parser_token_skips.h"

namespace delta {

Expr* ParserPropertySpecHelpers::OneLiteral(Parser& p) {
  auto* one = p.arena_.Create<Expr>();
  one->kind = ExprKind::kIntegerLiteral;
  one->text = "1";
  one->int_val = 1;
  one->range.start = p.CurrentToken().loc;
  return one;
}

bool ParserPropertySpecHelpers::ParseMatchItemTarget(Parser& p,
                                                     SeqMatchAssign& item) {
  if (!p.Check(TokenKind::kIdentifier)) return false;
  Token name = p.Consume();
  item.lvar = name.text;
  if (p.Check(TokenKind::kDot) || p.AtSelectBracket()) {
    item.target = p.ParseIdentifierPostfixChain(p.ParseMemberAccessChain(name));
  }
  return true;
}

bool ParserPropertySpecHelpers::ParseIncDecMatchItem(Parser& p,
                                                     SeqMatchAssign& item,
                                                     bool prefix) {
  TokenKind op = p.Consume().kind;
  if (prefix && !ParseMatchItemTarget(p, item)) return false;
  item.op =
      op == TokenKind::kPlusPlus ? TokenKind::kPlusEq : TokenKind::kMinusEq;
  item.rhs = OneLiteral(p);
  return true;
}

bool ParserPropertySpecHelpers::AheadIsSubroutineCall(Parser& p) {
  if (p.Check(TokenKind::kSystemIdentifier)) return true;
  if (!p.Check(TokenKind::kIdentifier)) return false;
  auto saved = p.lexer_.SavePos();
  p.Consume();
  while (p.Check(TokenKind::kDot) || p.Check(TokenKind::kColonColon)) {
    p.Consume();
    p.Consume();
  }
  bool call = p.Check(TokenKind::kLParen) || p.Check(TokenKind::kComma) ||
              p.Check(TokenKind::kRParen);
  p.lexer_.RestorePos(saved);
  return call;
}

Expr* ParserPropertySpecHelpers::ParseAttachedCall(Parser& p) {
  Expr* callee = p.ParseExpr();
  if (callee == nullptr || callee->kind == ExprKind::kCall ||
      callee->kind == ExprKind::kSystemCall) {
    return callee;
  }
  auto* call = p.arena_.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = callee->text;
  call->lhs = callee;
  call->range = callee->range;
  return call;
}

bool ParserPropertySpecHelpers::ParseSequenceMatchItem(Parser& p,
                                                       SeqMatchAssign& item) {
  if (AheadIsSubroutineCall(p)) {
    item.call = ParseAttachedCall(p);
    return item.call != nullptr;
  }
  if (p.Check(TokenKind::kPlusPlus) || p.Check(TokenKind::kMinusMinus)) {
    return ParseIncDecMatchItem(p, item, true);
  }
  if (!ParseMatchItemTarget(p, item)) return false;
  if (p.Check(TokenKind::kPlusPlus) || p.Check(TokenKind::kMinusMinus)) {
    return ParseIncDecMatchItem(p, item, false);
  }
  if (!p.Check(TokenKind::kEq) && !IsCompoundAssignOp(p.CurrentToken().kind)) {
    return false;
  }
  item.op = p.Consume().kind;
  item.rhs = p.ParseExpr();
  return item.rhs != nullptr;
}

bool ParserPropertySpecHelpers::ParseSequenceMatchItems(
    Parser& p, std::vector<SeqMatchAssign>& items) {
  while (p.Match(TokenKind::kComma)) {
    SeqMatchAssign item;
    if (!ParseSequenceMatchItem(p, item)) return false;
    items.push_back(item);
  }
  return true;
}

}  // namespace delta
