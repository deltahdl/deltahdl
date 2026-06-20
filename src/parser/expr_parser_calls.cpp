#include "parser/parser.h"

namespace delta {

Expr* Parser::ParseSystemCall() {
  auto tok = Consume();

  if (IsTimingCheckName(tok.text)) {
    diag_.Error(tok.loc, "timing check cannot appear in procedural code");
  }

  if (tok.text == "$unit" && Check(TokenKind::kColonColon)) {
    Consume();
    auto id = ExpectIdentifier();
    auto* expr = arena_.Create<Expr>();
    expr->kind = ExprKind::kIdentifier;
    expr->text = id.text;
    expr->scope_prefix = tok.text;
    expr->range.start = tok.loc;
    return expr;
  }
  if (tok.text == "$root" && Check(TokenKind::kDot)) {
    Consume();
    auto id = ExpectIdentifier();
    auto* expr = arena_.Create<Expr>();
    expr->kind = ExprKind::kIdentifier;
    expr->text = id.text;
    expr->scope_prefix = tok.text;
    expr->range.start = tok.loc;
    while (Check(TokenKind::kDot) || Check(TokenKind::kColonColon)) {
      expr = MakeMemberAccess(expr);
    }
    if (Check(TokenKind::kLBracket)) expr = ParseSelectExpr(expr);
    return expr;
  }
  auto* call = arena_.Create<Expr>();
  call->kind = ExprKind::kSystemCall;
  call->callee = tok.text;
  call->range.start = tok.loc;
  if (!Match(TokenKind::kLParen)) return call;
  if (!Check(TokenKind::kRParen)) {
    if (Check(TokenKind::kComma)) {
      call->args.push_back(nullptr);
    } else {
      call->args.push_back(ParseExpr());
    }
    while (Match(TokenKind::kComma)) {
      if (Check(TokenKind::kAt)) {
        // Annex C.2.2: the clocking event argument to $sampled was removed.
        // $sampled no longer depends on a clocking event, so the syntax that
        // once supplied one is no longer accepted. Other sampled value
        // functions still take a clocking event (see 16.9.3).
        if (call->callee == "$sampled") {
          diag_.Error(CurrentLoc(),
                      "$sampled does not accept a clocking event argument");
        }
        Consume();
        if (Match(TokenKind::kLParen)) {
          ParseEventList();
          Expect(TokenKind::kRParen);
        } else {
          Consume();
        }
        break;
      } else if (Check(TokenKind::kComma) || Check(TokenKind::kRParen)) {
        call->args.push_back(nullptr);
      } else {
        call->args.push_back(ParseExpr());
      }
    }
  }
  Expect(TokenKind::kRParen);
  return call;
}

Expr* Parser::ParseConcatenation() {
  auto loc = CurrentLoc();
  Expect(TokenKind::kLBrace);

  if (Check(TokenKind::kRBrace)) {
    Consume();
    auto* cat = arena_.Create<Expr>();
    cat->kind = ExprKind::kConcatenation;
    cat->range.start = loc;
    return cat;
  }

  if (Check(TokenKind::kLtLt) || Check(TokenKind::kGtGt)) {
    auto dir = CurrentToken().kind;
    auto* sc = ParseStreamingConcat(dir);
    Expect(TokenKind::kRBrace);
    return sc;
  }

  auto* first = ParseExpr();

  if (Check(TokenKind::kLBrace)) {
    Consume();
    auto* rep = arena_.Create<Expr>();
    rep->kind = ExprKind::kReplicate;
    rep->repeat_count = first;
    rep->range.start = loc;
    rep->elements.push_back(ParseExpr());
    while (Match(TokenKind::kComma)) {
      rep->elements.push_back(ParseExpr());
    }
    Expect(TokenKind::kRBrace);
    Expect(TokenKind::kRBrace);

    if (Check(TokenKind::kLBracket)) return ParseSelectExpr(rep);
    return rep;
  }

  auto* cat = arena_.Create<Expr>();
  cat->kind = ExprKind::kConcatenation;
  cat->range.start = loc;
  cat->elements.push_back(first);
  while (Match(TokenKind::kComma)) {
    cat->elements.push_back(ParseExpr());
  }
  Expect(TokenKind::kRBrace);

  if (Check(TokenKind::kLBracket)) return ParseSelectExpr(cat);
  return cat;
}

Expr* Parser::ParseCastExpr() {
  auto type_tok = Consume();
  Expect(TokenKind::kApostrophe);
  Expect(TokenKind::kLParen);
  auto* cast = arena_.Create<Expr>();
  cast->kind = ExprKind::kCast;
  cast->text = type_tok.text;
  cast->range.start = type_tok.loc;
  cast->lhs = ParseExpr();
  Expect(TokenKind::kRParen);
  return cast;
}

}  // namespace delta
