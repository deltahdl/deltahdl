#include "parser/parser.h"

namespace delta {

// Builds the scoped identifier expression produced by a "$unit::id" or
// "$root.id" system-keyword prefix (see 23.7.1 scope resolution /
// hierarchical names). The named scope keyword is recorded in scope_prefix.
Expr* Parser::MakeSysScopePrefix(const Token& sys_tok) {
  auto id = ExpectIdentifier();
  auto* expr = arena_.Create<Expr>();
  expr->kind = ExprKind::kIdentifier;
  expr->text = id.text;
  expr->scope_prefix = sys_tok.text;
  expr->range.start = sys_tok.loc;
  return expr;
}

// Parses the trailing select/event syntax of a "$root.id..." hierarchical
// name: any further member accesses followed by an optional bit/part select.
Expr* Parser::ParseSysRootTail(Expr* expr) {
  while (Check(TokenKind::kDot) || Check(TokenKind::kColonColon)) {
    expr = MakeMemberAccess(expr);
  }
  if (Check(TokenKind::kLBracket)) expr = ParseSelectExpr(expr);
  return expr;
}

// Consumes one "@event" clocking-event argument. Annex C.2.2: the clocking
// event argument to $sampled was removed, so $sampled no longer accepts one
// (other sampled value functions still take a clocking event, see 16.9.3).
void Parser::ParseSysClockingEventArg(Expr* call) {
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
}

// Parses the comma-separated argument list, appending each argument (or
// nullptr for an empty slot) to call->args; an "@event" terminates the list.
void Parser::ParseSysCallArgs(Expr* call) {
  if (Check(TokenKind::kComma)) {
    call->args.push_back(nullptr);
  } else {
    call->args.push_back(ParseExpr());
  }
  while (Match(TokenKind::kComma)) {
    if (Check(TokenKind::kAt)) {
      ParseSysClockingEventArg(call);
      break;
    }
    if (Check(TokenKind::kComma) || Check(TokenKind::kRParen)) {
      call->args.push_back(nullptr);
    } else {
      call->args.push_back(ParseExpr());
    }
  }
}

Expr* Parser::ParseSystemCall() {
  auto tok = Consume();

  if (IsTimingCheckName(tok.text)) {
    diag_.Error(tok.loc, "timing check cannot appear in procedural code");
  }

  if (tok.text == "$unit" && Check(TokenKind::kColonColon)) {
    Consume();
    return MakeSysScopePrefix(tok);
  }
  if (tok.text == "$root" && Check(TokenKind::kDot)) {
    Consume();
    return ParseSysRootTail(MakeSysScopePrefix(tok));
  }

  auto* call = arena_.Create<Expr>();
  call->kind = ExprKind::kSystemCall;
  call->callee = tok.text;
  call->range.start = tok.loc;
  if (!Match(TokenKind::kLParen)) {
    if (Check(TokenKind::kLBracket)) return ParseSelectExpr(call);
    return call;
  }

  if (!Check(TokenKind::kRParen)) {
    ParseSysCallArgs(call);
  }
  Expect(TokenKind::kRParen);
  if (Check(TokenKind::kLBracket)) return ParseSelectExpr(call);
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
