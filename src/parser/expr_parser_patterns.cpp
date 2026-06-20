#include "parser/parser.h"

namespace delta {

Expr* Parser::ParseTypeRefExpr() {
  auto loc = CurrentLoc();
  Consume();
  Expect(TokenKind::kLParen);
  auto* ref = arena_.Create<Expr>();
  ref->kind = ExprKind::kTypeRef;
  ref->range.start = loc;

  auto dtype = ParseDataType();
  if (dtype.kind != DataTypeKind::kImplicit) {
    ref->text = dtype.type_name;
  } else {
    ref->lhs = ParseExpr();
  }
  Expect(TokenKind::kRParen);
  return ref;
}

Expr* Parser::ParseMinTypMaxExpr() {
  auto* expr = ParseExpr();
  if (!Check(TokenKind::kColon)) return expr;
  Consume();
  auto* typ = ParseExpr();
  Expect(TokenKind::kColon);
  auto* max = ParseExpr();
  auto* mtm = arena_.Create<Expr>();
  mtm->kind = ExprKind::kMinTypMax;
  mtm->range.start = expr->range.start;
  mtm->lhs = expr;
  mtm->condition = typ;
  mtm->rhs = max;
  return mtm;
}

Expr* Parser::ParseInsideExpr(Expr* lhs) {
  Consume();
  auto* inside = arena_.Create<Expr>();
  inside->kind = ExprKind::kInside;
  inside->range.start = lhs->range.start;
  inside->lhs = lhs;
  Expect(TokenKind::kLBrace);
  ParseInsideRangeList(inside->elements);
  Expect(TokenKind::kRBrace);
  return inside;
}

void Parser::ParseInsideRangeList(std::vector<Expr*>& out) {
  out.push_back(ParseInsideValueRange());
  while (Match(TokenKind::kComma)) {
    out.push_back(ParseInsideValueRange());
  }
}

Expr* Parser::ParseInsideValueRange() {
  if (!Check(TokenKind::kLBracket)) return ParseExpr();
  Consume();
  auto* lo = ParseExpr();
  auto* range = arena_.Create<Expr>();
  range->kind = ExprKind::kSelect;
  range->index = lo;

  if (Check(TokenKind::kPlusSlashMinus) ||
      Check(TokenKind::kPlusPercentMinus)) {
    range->op = CurrentToken().kind;
    Consume();
    range->index_end = ParseExpr();
    Expect(TokenKind::kRBracket);
    return range;
  }

  Expect(TokenKind::kColon);
  range->index_end = ParseExpr();
  Expect(TokenKind::kRBracket);
  return range;
}

}  // namespace delta
