#include "parser/parser.h"

namespace delta {

Expr* Parser::ParseTypeRefExpr() {
  auto loc = CurrentLoc();
  Consume();  // 'type'
  Expect(TokenKind::kLParen);
  auto* ref = arena_.Create<Expr>();
  ref->kind = ExprKind::kTypeRef;
  ref->range.start = loc;
  // Try parsing as data type first: type(logic[11:0]) (§6.23)
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
  Consume();  // first ':'
  auto* typ = ParseExpr();
  Expect(TokenKind::kColon);
  auto* max = ParseExpr();
  auto* mtm = arena_.Create<Expr>();
  mtm->kind = ExprKind::kMinTypMax;
  mtm->range.start = expr->range.start;
  mtm->lhs = expr;       // min
  mtm->condition = typ;  // typ
  mtm->rhs = max;        // max
  return mtm;
}

Expr* Parser::ParseInsideExpr(Expr* lhs) {
  Consume();  // 'inside'
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
  // §11.4.13: Range syntax variants.
  if (!Check(TokenKind::kLBracket)) return ParseExpr();
  Consume();
  auto* lo = ParseExpr();
  auto* range = arena_.Create<Expr>();
  range->kind = ExprKind::kSelect;
  range->index = lo;
  // Tolerance: [A +/- B] or [A +%- B].
  if (Check(TokenKind::kPlusSlashMinus) ||
      Check(TokenKind::kPlusPercentMinus)) {
    range->op = CurrentToken().kind;
    Consume();
    range->index_end = ParseExpr();
    Expect(TokenKind::kRBracket);
    return range;
  }
  // Normal range: [lo:hi], [$:hi], [lo:$].
  Expect(TokenKind::kColon);
  range->index_end = ParseExpr();
  Expect(TokenKind::kRBracket);
  return range;
}

}  // namespace delta
