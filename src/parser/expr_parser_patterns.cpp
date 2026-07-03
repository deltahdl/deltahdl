#include "parser/expr_parser_internal.h"
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

static bool IsAssignmentPatternKey(TokenKind k) {
  switch (k) {
    case TokenKind::kIdentifier:
    case TokenKind::kKwDefault:
    case TokenKind::kIntLiteral:
    case TokenKind::kKwInt:
    case TokenKind::kKwReal:
    case TokenKind::kKwLogic:
    case TokenKind::kKwByte:
    case TokenKind::kKwShortint:
    case TokenKind::kKwLongint:
    case TokenKind::kKwShortreal:
    case TokenKind::kKwInteger:
    case TokenKind::kKwBit:
    case TokenKind::kKwReg:
    case TokenKind::kKwTime:
    case TokenKind::kKwRealtime:
    case TokenKind::kKwString:
    case TokenKind::kStringLiteral:
      return true;
    default:
      return false;
  }
}

Expr* Parser::ParsePatternReplication(Expr* count, SourceLoc loc) {
  Consume();
  auto* rep = arena_.Create<Expr>();
  rep->kind = ExprKind::kReplicate;
  rep->repeat_count = count;
  rep->range.start = loc;
  rep->elements.push_back(ParseExpr());
  while (Match(TokenKind::kComma)) {
    rep->elements.push_back(ParseExpr());
  }
  Expect(TokenKind::kRBrace);
  return rep;
}

bool Parser::ParseFirstPatternElement(Expr* pat, bool& named) {
  if (Check(TokenKind::kDot)) {
    auto loc = CurrentLoc();
    Consume();
    auto name = ExpectIdentifier();
    auto* id = arena_.Create<Expr>();
    id->kind = ExprKind::kIdentifier;
    id->text = name.text;
    id->range.start = loc;
    // §12.6: `. variable_identifier` inside a `'{...}` structure pattern binds
    // a new pattern identifier; mark it for the elaborator's uniqueness check.
    id->is_pattern_binding = true;
    pat->elements.push_back(id);
    return true;
  }
  auto first = CurrentToken();
  if (!IsAssignmentPatternKey(first.kind)) {
    pat->elements.push_back(ParseExpr());
    return true;
  }
  Consume();
  if (Check(TokenKind::kColon)) {
    named = true;
    pat->pattern_keys.push_back(first.text);
    Consume();
    pat->elements.push_back(ParseExpr());
    return true;
  }
  auto* id = arena_.Create<Expr>();
  if (first.kind == TokenKind::kIntLiteral) {
    id->kind = ExprKind::kIntegerLiteral;
    id->text = first.text;
    id->int_val = ParseIntText(first.text);
  } else {
    id->kind = ExprKind::kIdentifier;
    id->text = first.text;
  }
  id->range.start = first.loc;
  id = ParseIdentifierPostfixChain(id);
  pat->elements.push_back(ParseInfixBp(id, 0));
  return true;
}

Expr* Parser::ParseAssignmentPattern() {
  auto loc = CurrentLoc();
  Expect(TokenKind::kApostropheLBrace);
  auto* pat = arena_.Create<Expr>();
  pat->kind = ExprKind::kAssignmentPattern;
  pat->range.start = loc;

  if (Check(TokenKind::kRBrace)) {
    Consume();
    return pat;
  }

  bool named = false;
  ParseFirstPatternElement(pat, named);

  if (!named && Check(TokenKind::kLBrace)) {
    auto* count = pat->elements[0];
    pat->elements.clear();
    pat->elements.push_back(ParsePatternReplication(count, loc));
    Expect(TokenKind::kRBrace);
    return pat;
  }

  while (Match(TokenKind::kComma)) {
    if (named) {
      auto key_tok = Consume();
      pat->pattern_keys.push_back(key_tok.text);
      Expect(TokenKind::kColon);
    }

    if (Check(TokenKind::kDot)) {
      Consume();
      auto name = ExpectIdentifier();
      auto* id = arena_.Create<Expr>();
      id->kind = ExprKind::kIdentifier;
      id->text = name.text;
      id->range.start = name.loc;
      // §12.6: subsequent `. variable_identifier` structure-pattern bindings
      // are marked the same way for the elaborator's uniqueness check.
      id->is_pattern_binding = true;
      pat->elements.push_back(id);
    } else {
      pat->elements.push_back(ParseExpr());
    }
  }

  Expect(TokenKind::kRBrace);
  return pat;
}

}  // namespace delta
