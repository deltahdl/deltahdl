#include "parser/expr_parser_internal.h"
#include "parser/parser.h"

namespace delta {

Expr* Parser::ParseTypeRefExpr() {
  auto loc = CurrentLoc();
  Consume();
  Expect(TokenKind::kLParen, Subclause::Unread());
  auto* ref = arena_.Create<Expr>();
  ref->kind = ExprKind::kTypeRef;
  ref->range.start = loc;

  auto dtype = ParseDataType();
  if (dtype.kind != DataTypeKind::kImplicit) {
    ref->text = dtype.type_name;
  } else {
    ref->lhs = ParseExpr();
  }
  Expect(TokenKind::kRParen, Subclause::Unread());
  return ref;
}

Expr* Parser::ParseMinTypMaxExpr() {
  auto* expr = ParseExpr();
  if (!Check(TokenKind::kColon)) return expr;
  Consume();
  auto* typ = ParseExpr();
  Expect(TokenKind::kColon, Subclause::Unread());
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
  Expect(TokenKind::kLBrace, Subclause::Unread());
  ParseInsideRangeList(inside->elements);
  Expect(TokenKind::kRBrace, Subclause::Unread());
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
    Expect(TokenKind::kRBracket, Subclause::Unread());
    return range;
  }

  Expect(TokenKind::kColon, Subclause::Unread());
  range->index_end = ParseExpr();
  Expect(TokenKind::kRBracket, Subclause::Unread());
  return range;
}

// §10.9: the keys Syntax 10-5 does not write as an expression --
// `assignment_pattern_key ::= simple_type | default`, where simple_type covers
// the integer and real type keywords. Every other key the syntax admits is a
// constant_expression or a member_identifier, both of which read as
// expressions; these two do not, so they are recognized by their keyword.
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
  rep->range.start = loc;
  rep->elements.push_back(ParseExpr());
  while (Match(TokenKind::kComma)) {
    rep->elements.push_back(ParseExpr());
  }
  Expect(TokenKind::kRBrace, Subclause::Unread());
  return rep;
}

// §12.6: `. variable_identifier` inside a `'{...}` structure pattern binds a
// new pattern identifier; mark it for the elaborator's uniqueness check.
Expr* Parser::ParsePatternBinding() {
  auto loc = CurrentLoc();
  Consume();
  auto name = ExpectIdentifier(Subclause::Unread());
  auto* id = arena_.Create<Expr>();
  id->kind = ExprKind::kIdentifier;
  id->text = name.text;
  id->range.start = loc;
  id->is_pattern_binding = true;
  return id;
}

// §10.9: a key written as one of the two keywords Syntax 10-5 gives for
// `assignment_pattern_key`. Neither is something an expression parse can read,
// so they are taken here, and only when a colon follows -- a keyword standing
// anywhere else in a pattern is not a key and is left where it was found. The
// colon itself is left for the caller to consume, so the two ways of writing a
// key end at the same place. Returns null when no such key stands here.
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

// §10.9: reads one element of an assignment pattern. Syntax 10-5 offers a
// keyed form and a positional one,
//
//   assignment_pattern ::= ' { expression { , expression } }
//                        | ' { array_pattern_key : expression { ... } }
//
// and what tells them apart is the colon that follows a key. A key is a
// constant_expression, `N-1` as legal a one as `3`, so the deciding colon may
// stand any distance into the element. The element is therefore read as an
// expression first, and a colon behind it is what turns what was read into the
// key of the value that follows. Reading a fixed number of tokens instead can
// only recognize the keys it was written to recognize: reading exactly one left
// every key of more than one token unparsed, and building a substitute node
// from that token turned a string literal into an identifier bearing the
// literal's text.
void Parser::ParsePatternElement(Expr* pat, bool& named) {
  if (Check(TokenKind::kDot)) {
    pat->elements.push_back(ParsePatternBinding());
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
  Expect(TokenKind::kColon, Subclause::Unread());
  named = true;
  pat->pattern_keys.push_back(key);
  pat->elements.push_back(Check(TokenKind::kDot) ? ParsePatternBinding()
                                                 : ParseExpr());
}

Expr* Parser::ParseAssignmentPattern() {
  auto loc = CurrentLoc();
  Expect(TokenKind::kApostropheLBrace, Subclause::Unread());
  auto* pat = arena_.Create<Expr>();
  pat->kind = ExprKind::kAssignmentPattern;
  pat->range.start = loc;

  if (Check(TokenKind::kRBrace)) {
    Consume();
    return pat;
  }

  bool named = false;
  ParsePatternElement(pat, named);

  if (!named && Check(TokenKind::kLBrace)) {
    auto* count = pat->elements[0];
    pat->elements.clear();
    pat->elements.push_back(ParsePatternReplication(count, loc));
    Expect(TokenKind::kRBrace, Subclause::Unread());
    return pat;
  }

  while (Match(TokenKind::kComma)) {
    bool was_named = named;
    size_t keys_before = pat->pattern_keys.size();
    ParsePatternElement(pat, named);
    // §10.9: Syntax 10-5 gives the keyed form and the positional one as
    // alternatives, so a pattern that has begun writing keys writes one for
    // every element from there on.
    if (was_named && pat->pattern_keys.size() == keys_before) {
      diag_.Error(CurrentLoc(),
                  "assignment pattern element after a keyed element needs a "
                  "key of its own",
                  Subclause("10.9"));
    }
  }

  Expect(TokenKind::kRBrace, Subclause::Unread());
  return pat;
}

}  // namespace delta
