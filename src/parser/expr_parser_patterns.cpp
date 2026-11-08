#include <cstddef>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "parser/expr_parser_internal.h"
#include "parser/parser.h"

namespace delta {

Expr* Parser::ParseTypeRefExpr() {
  auto loc = CurrentLoc();
  Consume();
  Expect(TokenKind::kLParen, Subclause("6.23"));
  auto* ref = arena_.Create<Expr>();
  ref->kind = ExprKind::kTypeRef;
  ref->range.start = loc;

  auto saved = lexer_.SavePos();
  auto dtype = ParseDataType();
  bool calls_scoped_method = dtype.kind == DataTypeKind::kNamed &&
                             !dtype.scope_name.empty() &&
                             Check(TokenKind::kLParen);
  if (Check(TokenKind::kApostrophe) || Check(TokenKind::kApostropheLBrace) ||
      calls_scoped_method) {
    lexer_.RestorePos(saved);
    dtype = DataType{};
  }
  if (dtype.kind != DataTypeKind::kImplicit) {
    ref->text = dtype.type_name;
    ref->scope_prefix = dtype.scope_name;
    ref->type_value = arena_.Create<DataType>(dtype);
  } else {
    ref->lhs = ParseExpr();
  }
  Expect(TokenKind::kRParen, Subclause("6.23"));
  return ref;
}

Expr* Parser::ParseMinTypMaxExpr() {
  auto* expr = ParseExpr();
  if (!Check(TokenKind::kColon)) return expr;
  Consume();
  auto* typ = ParseExpr();
  Expect(TokenKind::kColon, Subclause("11.11"));
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
  Expect(TokenKind::kLBrace, Subclause("11.4.13"));
  ParseInsideRangeList(inside->elements);
  Expect(TokenKind::kRBrace, Subclause("11.4.13"));
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
  SourceLoc loc = CurrentLoc();
  Consume();
  auto* lo = ParseExpr();
  auto* range = arena_.Create<Expr>();
  range->kind = ExprKind::kSelect;
  range->range.start = loc;
  range->index = lo;

  if (Check(TokenKind::kPlusSlashMinus) ||
      Check(TokenKind::kPlusPercentMinus)) {
    range->op = CurrentToken().kind;
    Consume();
    range->index_end = ParseExpr();
    Expect(TokenKind::kRBracket, Subclause("11.4.13"));
    return range;
  }

  Expect(TokenKind::kColon, Subclause("11.4.13"));
  range->index_end = ParseExpr();
  Expect(TokenKind::kRBracket, Subclause("11.4.13"));
  return range;
}

static bool IsAssignmentPatternKeyword(TokenKind k) {
  switch (k) {
    case TokenKind::kKwDefault:
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
  rep->is_pattern_replication = true;
  rep->range.start = loc;
  int depth = std::exchange(pattern_depth_, 0);
  rep->elements.push_back(ParseExpr());
  while (Match(TokenKind::kComma)) {
    rep->elements.push_back(ParseExpr());
  }
  pattern_depth_ = depth;
  Expect(TokenKind::kRBrace, Subclause("10.9.1"));
  return rep;
}

Expr* Parser::ParseDotPattern() {
  auto loc = CurrentLoc();
  if (pattern_depth_ == 0) {
    diag_.Error(loc,
                "'.name' and '.*' are patterns, which stand only after "
                "'matches' or in a pattern-matching case item",
                Subclause("A.6.7.1"));
  }
  if (Consume().Is(TokenKind::kDotStar)) {
    return MakeIdentifierNode(arena_, ".*", loc);
  }
  auto name = ExpectIdentifier(Subclause("12.6"));
  auto* id = MakeIdentifierNode(arena_, name.text, loc);
  id->is_pattern_binding = true;
  return id;
}

Expr* Parser::ParsePatternKeyword() {
  auto tok = CurrentToken();
  if (!IsAssignmentPatternKeyword(tok.kind)) return nullptr;
  auto saved = lexer_.SavePos();
  Consume();
  if (!Check(TokenKind::kColon)) {
    lexer_.RestorePos(saved);
    return nullptr;
  }
  auto* key = arena_.Create<Expr>();
  key->kind = ExprKind::kIdentifier;
  key->text = tok.text;
  key->range.start = tok.loc;
  return key;
}

void Parser::ParsePatternElement(Expr* pat, bool& named) {
  if (Check(TokenKind::kDot)) {
    pat->elements.push_back(ParseDotPattern());
    return;
  }
  Expr* key = ParsePatternKeyword();
  if (key == nullptr) {
    auto* head = ParseExpr();
    if (!Check(TokenKind::kColon)) {
      pat->elements.push_back(head);
      return;
    }
    key = head;
  }
  Expect(TokenKind::kColon, Subclause("10.9"));
  named = true;
  pat->pattern_keys.push_back(key);
  pat->elements.push_back(Check(TokenKind::kDot) ? ParseDotPattern()
                                                 : ParseExpr());
}

Expr* Parser::ParseAssignmentPattern() {
  auto loc = CurrentLoc();
  Expect(TokenKind::kApostropheLBrace, Subclause("10.9"));
  auto* pat = arena_.Create<Expr>();
  pat->kind = ExprKind::kAssignmentPattern;
  pat->range.start = loc;

  if (Check(TokenKind::kRBrace)) {
    diag_.Error(CurrentLoc(),
                "assignment pattern needs at least one expression",
                Subclause("10.9"));
    Consume();
    return pat;
  }

  bool named = false;
  ParsePatternElement(pat, named);

  if (!named && Check(TokenKind::kLBrace)) {
    auto* count = pat->elements[0];
    pat->elements.clear();
    pat->elements.push_back(ParsePatternReplication(count, loc));
    Expect(TokenKind::kRBrace, Subclause("10.9"));
    return pat;
  }

  while (Match(TokenKind::kComma)) {
    bool was_named = named;
    size_t keys_before = pat->pattern_keys.size();
    ParsePatternElement(pat, named);
    if (was_named && pat->pattern_keys.size() == keys_before) {
      diag_.Error(CurrentLoc(),
                  "assignment pattern element after a keyed element needs a "
                  "key of its own",
                  Subclause("10.9"));
    }
    if (!was_named && named) {
      diag_.Error(CurrentLoc(),
                  "a keyed assignment pattern element cannot follow a "
                  "positional one",
                  Subclause("10.9"));
    }
  }

  Expect(TokenKind::kRBrace, Subclause("10.9"));
  return pat;
}

}  // namespace delta
