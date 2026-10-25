// IEEE 1800-2023 §16.10 and §16.11's sequence_match_items as the parser's
// linear capture of a sequence reads them: a local variable's assignment, an
// inc_or_dec_expression, and a subroutine call attached to the sequence, each
// recorded as one SeqMatchAssign.
//
// These are their own translation unit rather than part of
// src/parser/parser_sequence_linear.cpp, which reached the limit
// assert-no-oversized-source-files enforces when a call written with no list
// of arguments began to be read as one, and a group's match items after a
// repeated operand began to be kept apart from it.

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

// §16.10: the variable_lvalue a match item writes, the local's name and,
// where A.10 footnote 51 lets it select within the local or name a member of
// it, `v[1]` or `s.f`, the whole of what is written as `target`.
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

// §16.10: an inc_or_dec_expression as a match item, `lvar++`, `lvar--`,
// `++lvar` or `--lvar`, is the local updated by one, `lvar += 1` or `lvar
// -= 1`; `prefix` says the operator stood before the name.
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

// §16.11: whether the tokens ahead are a subroutine call rather than the
// local an assignment begins with: a system task's name, or a name followed
// by `(` or ending the match item, since A.8.2's tf_call and method_call
// write their list of arguments as optional. The name may be dotted or
// scoped, a method called through a handle, `cg_1.sample()` (§17.6), or a
// subroutine of a package or class, `p::f()`. The lexer is rewound.
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

// §16.11: the subroutine call a match item makes. A name written with no
// list of arguments is the call it would be with an empty one, so the call
// is recorded as Parser::ParseCallExpr records `name()`.
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

// One match item: §16.11's subroutine call, an inc_or_dec_expression in
// either form, or `lvar = rhs` or `lvar op= rhs`.
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

// §16.10: the match items after a group's sequence_expr, each `lvar = rhs`,
// `lvar op= rhs`, an inc_or_dec_expression or a subroutine call.
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
