#include "parser/parser.h"

namespace delta {

Expr* Parser::ParseStreamingConcat(TokenKind dir) {
  auto loc = CurrentLoc();
  Consume();
  auto* sc = arena_.Create<Expr>();
  sc->kind = ExprKind::kStreamingConcat;
  sc->range.start = loc;
  sc->op = dir;

  if (!Check(TokenKind::kLBrace)) {
    auto saved = lexer_.SavePos();
    auto tok = Consume();
    if (Check(TokenKind::kLBrace)) {
      auto* type_id = arena_.Create<Expr>();
      type_id->kind = ExprKind::kIdentifier;
      type_id->text = tok.text;
      type_id->range.start = tok.loc;
      sc->lhs = type_id;
    } else {
      lexer_.RestorePos(saved);
      sc->lhs = ParsePrimaryExpr();
    }
  }

  Expect(TokenKind::kLBrace);
  sc->elements.push_back(ParseExpr());
  while (Match(TokenKind::kComma)) {
    sc->elements.push_back(ParseExpr());
  }
  Expect(TokenKind::kRBrace);
  return sc;
}

void Parser::ParseNamedArg(Expr* call) {
  Expect(TokenKind::kDot);
  auto name_tok = Expect(TokenKind::kIdentifier);
  Expect(TokenKind::kLParen);
  Expr* value = nullptr;
  if (!Check(TokenKind::kRParen)) {
    value = ParseExpr();
  }
  Expect(TokenKind::kRParen);
  call->arg_names.push_back(name_tok.text);
  call->args.push_back(value);
}

Expr* Parser::ParseCompoundAssignExpr(Expr* lhs) {
  auto op_tok = Consume();
  auto* rhs = ParseExpr();
  auto* bin = arena_.Create<Expr>();
  bin->kind = ExprKind::kBinary;
  bin->op = op_tok.kind;
  bin->lhs = lhs;
  bin->rhs = rhs;
  bin->range.start = lhs->range.start;
  return bin;
}

Expr* Parser::ParseParenExpr() {
  Consume();
  auto* lhs = ParseExpr();

  auto k = CurrentToken().kind;
  bool is_assign = k == TokenKind::kEq || k == TokenKind::kPlusEq ||
                   k == TokenKind::kMinusEq || k == TokenKind::kStarEq ||
                   k == TokenKind::kSlashEq || k == TokenKind::kPercentEq ||
                   k == TokenKind::kAmpEq || k == TokenKind::kPipeEq ||
                   k == TokenKind::kCaretEq || k == TokenKind::kLtLtEq ||
                   k == TokenKind::kGtGtEq || k == TokenKind::kLtLtLtEq ||
                   k == TokenKind::kGtGtGtEq;
  if (is_assign) {
    auto op_tok = Consume();
    auto* rhs = ParseExpr();
    auto* bin = arena_.Create<Expr>();
    bin->kind = ExprKind::kBinary;
    bin->op = op_tok.kind;
    bin->lhs = lhs;
    bin->rhs = rhs;
    bin->range.start = lhs->range.start;
    lhs = bin;
  }
  Expect(TokenKind::kRParen);

  if (Check(TokenKind::kApostrophe)) {
    Consume();
    Expect(TokenKind::kLParen);
    auto* cast = arena_.Create<Expr>();
    cast->kind = ExprKind::kCast;
    cast->range.start = lhs->range.start;
    cast->lhs = ParseExpr();
    cast->rhs = lhs;
    Expect(TokenKind::kRParen);
    return cast;
  }
  lhs->is_parenthesized = true;
  return lhs;
}

}  // namespace delta
