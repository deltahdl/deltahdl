#include <charconv>
#include <cstdlib>

#include "parser/parser.h"

namespace delta {

static bool IsCastTypeToken(TokenKind kind) {
  switch (kind) {
    case TokenKind::kKwInt:
    case TokenKind::kKwLogic:
    case TokenKind::kKwBit:
    case TokenKind::kKwByte:
    case TokenKind::kKwShortint:
    case TokenKind::kKwLongint:
    case TokenKind::kKwInteger:
    case TokenKind::kKwReal:
    case TokenKind::kKwShortreal:
    case TokenKind::kKwReg:
    case TokenKind::kKwSigned:
    case TokenKind::kKwUnsigned:
    case TokenKind::kKwString:
    case TokenKind::kKwConst:
      return true;
    default:
      return false;
  }
}

// Parse a SystemVerilog integer literal text into a uint64_t value.
// Handles: decimal "42", based "8'hFF", underscore "1_000".
static uint64_t ParseIntText(std::string_view text) {
  // Strip underscores into a local buffer.
  std::string buf;
  buf.reserve(text.size());
  for (char c : text) {
    if (c != '_') buf.push_back(c);
  }

  // Find tick for based literals (e.g., 8'hFF).
  auto tick = buf.find('\'');
  if (tick == std::string::npos) {
    uint64_t val = 0;
    std::from_chars(buf.data(), buf.data() + buf.size(), val, 10);
    return val;
  }

  // Skip optional 's' after tick, then parse base letter.
  size_t i = tick + 1;
  if (i < buf.size() && (buf[i] == 's' || buf[i] == 'S')) ++i;
  int base = 10;
  if (i < buf.size()) {
    switch (buf[i]) {
      case 'h':
      case 'H':
        base = 16;
        break;
      case 'b':
      case 'B':
        base = 2;
        break;
      case 'o':
      case 'O':
        base = 8;
        break;
      default:
        break;
    }
    ++i;
  }
  uint64_t val = 0;
  std::from_chars(buf.data() + i, buf.data() + buf.size(), val, base);
  return val;
}

// Parse a SystemVerilog real or time literal text into a double value.
// Handles: fixed "3.14", exponent "1e10", underscore "1_000.5".
// For time literals (e.g., "100ns"), strtod stops at the suffix.
static double ParseRealText(std::string_view text) {
  std::string buf;
  buf.reserve(text.size());
  for (char c : text) {
    if (c != '_') buf.push_back(c);
  }
  return std::strtod(buf.c_str(), nullptr);
}

// Pratt parser: binding powers for SystemVerilog operators (IEEE 1800-2023 §11)
// Higher binding power = tighter binding

static std::pair<int, int> InfixBp(TokenKind kind) {
  switch (kind) {
    case TokenKind::kPipeDashGt:
    case TokenKind::kPipeEqGt:
      return {1, 2};
    case TokenKind::kPipePipe:
      return {3, 4};
    case TokenKind::kAmpAmp:
      return {5, 6};
    case TokenKind::kPipe:
      return {7, 8};
    case TokenKind::kCaret:
    case TokenKind::kCaretTilde:
    case TokenKind::kTildeCaret:
      return {9, 10};
    case TokenKind::kAmp:
      return {11, 12};
    case TokenKind::kEqEq:
    case TokenKind::kBangEq:
    case TokenKind::kEqEqEq:
    case TokenKind::kBangEqEq:
    case TokenKind::kEqEqQuestion:
    case TokenKind::kBangEqQuestion:
      return {13, 14};
    case TokenKind::kLt:
    case TokenKind::kGt:
    case TokenKind::kLtEq:
    case TokenKind::kGtEq:
      return {15, 16};
    case TokenKind::kLtLt:
    case TokenKind::kGtGt:
    case TokenKind::kLtLtLt:
    case TokenKind::kGtGtGt:
      return {17, 18};
    case TokenKind::kPlus:
    case TokenKind::kMinus:
      return {19, 20};
    case TokenKind::kStar:
    case TokenKind::kSlash:
    case TokenKind::kPercent:
      return {21, 22};
    case TokenKind::kPower:
      return {24, 23};  // right-assoc
    default:
      return {-1, -1};
  }
}

static int PrefixBp(TokenKind kind) {
  switch (kind) {
    case TokenKind::kPlus:
    case TokenKind::kMinus:
    case TokenKind::kBang:
    case TokenKind::kTilde:
    case TokenKind::kAmp:
    case TokenKind::kTildeAmp:
    case TokenKind::kPipe:
    case TokenKind::kTildePipe:
    case TokenKind::kCaret:
    case TokenKind::kTildeCaret:
    case TokenKind::kCaretTilde:
      return 25;
    default:
      return -1;
  }
}

Expr* Parser::ParseExpr() { return ParseExprBp(0); }

Expr* Parser::ParseExprBp(int min_bp) {
  auto* lhs = ParsePrefixExpr();
  return ParseInfixBp(lhs, min_bp);
}

Expr* Parser::ParseInfixBp(Expr* lhs, int min_bp) {
  while (true) {
    auto tok = CurrentToken();
    if (tok.IsEof()) {
      break;
    }

    // Ternary: expr ? (* attr *) expr : expr
    if (tok.kind == TokenKind::kQuestion && min_bp <= 1) {
      Consume();
      ParseAttributes();  // optional attribute before true-branch
      auto* tern = arena_.Create<Expr>();
      tern->kind = ExprKind::kTernary;
      tern->condition = lhs;
      tern->true_expr = ParseExprBp(0);
      Expect(TokenKind::kColon);
      tern->false_expr = ParseExprBp(0);
      lhs = tern;
      continue;
    }

    // inside expression: expr inside { range_list }
    if (tok.kind == TokenKind::kKwInside && min_bp <= 1) {
      lhs = ParseInsideExpr(lhs);
      continue;
    }

    // §12.6: matches expression — expr matches pattern
    if (tok.kind == TokenKind::kKwMatches && min_bp <= 1) {
      Consume();
      auto* bin = arena_.Create<Expr>();
      bin->kind = ExprKind::kBinary;
      bin->op = TokenKind::kKwMatches;
      bin->lhs = lhs;
      bin->rhs = ParseExprBp(2);
      lhs = bin;
      continue;
    }

    auto [lbp, rbp] = InfixBp(tok.kind);
    if (lbp < 0 || lbp < min_bp) {
      break;
    }

    auto op = Consume();
    ParseAttributes();  // optional attribute before RHS operand
    auto* rhs = ParseExprBp(rbp);
    auto* bin = arena_.Create<Expr>();
    bin->kind = ExprKind::kBinary;
    bin->op = op.kind;
    bin->lhs = lhs;
    bin->rhs = rhs;
    bin->range.start = lhs->range.start;
    lhs = bin;
  }
  return lhs;
}

Expr* Parser::ParsePrefixExpr() {
  auto tok = CurrentToken();

  // Prefix increment/decrement (§11.4.2)
  if (tok.kind == TokenKind::kPlusPlus || tok.kind == TokenKind::kMinusMinus) {
    auto op = Consume();
    auto* operand = ParsePrimaryExpr();
    auto* unary = arena_.Create<Expr>();
    unary->kind = ExprKind::kUnary;
    unary->op = op.kind;
    unary->lhs = operand;
    unary->range.start = op.loc;
    return unary;
  }

  int bp = PrefixBp(tok.kind);
  if (bp >= 0) {
    auto op = Consume();
    auto* operand = ParseExprBp(bp);
    auto* unary = arena_.Create<Expr>();
    unary->kind = ExprKind::kUnary;
    unary->op = op.kind;
    unary->lhs = operand;
    unary->range.start = op.loc;
    return unary;
  }
  return ParsePrimaryExpr();
}

Expr* Parser::MakeLiteral(ExprKind kind, const Token& tok) {
  Consume();
  auto* lit = arena_.Create<Expr>();
  lit->kind = kind;
  lit->text = tok.text;
  lit->range.start = tok.loc;
  if (kind == ExprKind::kIntegerLiteral) {
    lit->int_val = ParseIntText(tok.text);
  } else if (kind == ExprKind::kRealLiteral || kind == ExprKind::kTimeLiteral) {
    lit->real_val = ParseRealText(tok.text);
  }
  return lit;
}

Expr* Parser::ParseNewExpr() {
  auto* expr = arena_.Create<Expr>();
  expr->kind = ExprKind::kCall;
  expr->text = "new";
  expr->range.start = Consume().loc;
  if (Check(TokenKind::kLBracket)) {
    // §7.5.1: new[size] — dynamic array constructor
    Consume();
    expr->args.push_back(ParseExpr());
    Expect(TokenKind::kRBracket);
    if (Check(TokenKind::kLParen)) ParseParenList(expr->args);
  } else if (Check(TokenKind::kLParen)) {
    ParseParenList(expr->args);
  }
  // §8.12 shallow copy: new <identifier>
  if (CheckIdentifier()) expr->lhs = ParseExpr();
  return expr;
}

Expr* Parser::ParseTaggedExpr() {
  auto* expr = arena_.Create<Expr>();
  expr->kind = ExprKind::kIdentifier;
  expr->text = "tagged";
  expr->range.start = Consume().loc;
  auto member_tok = ExpectIdentifier();
  auto* member = arena_.Create<Expr>();
  member->kind = ExprKind::kIdentifier;
  member->text = member_tok.text;
  member->range.start = member_tok.loc;
  expr->rhs = member;
  if (Check(TokenKind::kLParen)) {
    Consume();
    expr->lhs = ParseExpr();
    Expect(TokenKind::kRParen);
  } else if (Check(TokenKind::kApostropheLBrace)) {
    expr->lhs = ParseAssignmentPattern();
  }
  return expr;
}

Expr* Parser::ParsePrimaryExpr() {
  auto tok = CurrentToken();

  // clang-format off
  switch (tok.kind) {
    case TokenKind::kIntLiteral:
    case TokenKind::kUnbasedUnsizedLiteral:
      return MakeLiteral(ExprKind::kIntegerLiteral, tok);
    case TokenKind::kRealLiteral:
      return MakeLiteral(ExprKind::kRealLiteral, tok);
    case TokenKind::kTimeLiteral:
      return MakeLiteral(ExprKind::kTimeLiteral, tok);
    case TokenKind::kStringLiteral:
      return MakeLiteral(ExprKind::kStringLiteral, tok);
    case TokenKind::kSystemIdentifier:
      return ParseSystemCall();
    case TokenKind::kIdentifier:
    case TokenKind::kEscapedIdentifier:
      return ParseIdentifierExpr();
    case TokenKind::kLParen:
      return ParseParenExpr();
    case TokenKind::kLBrace:
      return ParseConcatenation();
    case TokenKind::kApostropheLBrace:
      return ParseAssignmentPattern();
    case TokenKind::kKwType:
      return ParseTypeRefExpr();
    case TokenKind::kDollar:  // §6.20.7
    case TokenKind::kKwNull:  // §8.4
      return MakeLiteral(ExprKind::kIdentifier, tok);
    case TokenKind::kKwThis:
    case TokenKind::kKwSuper: {                          // §8.11/§8.15
      Expr* result = ParseMemberAccessChain(Consume());
      if (Check(TokenKind::kLParen)) result = ParseCallExpr(result);
      if (Check(TokenKind::kLBracket)) result = ParseSelectExpr(result);
      return ParseWithClause(result);
    }
    case TokenKind::kKwTagged:                            // §11.9
      return ParseTaggedExpr();
    case TokenKind::kKwNew:                               // §8.7
      return ParseNewExpr();
    default:
      break;
  }
  // clang-format on

  if (IsCastTypeToken(tok.kind)) return ParseCastExpr();

  diag_.Error(tok.loc, "expected expression");
  Consume();
  auto* err = arena_.Create<Expr>();
  err->kind = ExprKind::kIntegerLiteral;
  err->range.start = tok.loc;
  return err;
}

// Build a member-access node: consumes '.' or '::' then the member name.
// Accepts 'new' as member name for super.new() (§8.15).
Expr* Parser::MakeMemberAccess(Expr* base) {
  Consume();  // '.' or '::'
  auto member_tok = Check(TokenKind::kKwNew) ? Consume() : ExpectIdentifier();
  auto* member_id = arena_.Create<Expr>();
  member_id->kind = ExprKind::kIdentifier;
  member_id->text = member_tok.text;
  member_id->range.start = member_tok.loc;
  auto* acc = arena_.Create<Expr>();
  acc->kind = ExprKind::kMemberAccess;
  acc->lhs = base;
  acc->rhs = member_id;
  acc->range.start = base->range.start;
  return acc;
}

Expr* Parser::ParseMemberAccessChain(Token tok) {
  auto* id = arena_.Create<Expr>();
  id->kind = ExprKind::kIdentifier;
  id->text = tok.text;
  id->range.start = tok.loc;
  Expr* result = id;
  while (Check(TokenKind::kDot) || Check(TokenKind::kColonColon)) {
    result = MakeMemberAccess(result);
  }
  return result;
}

Expr* Parser::ParseIdentifierExpr() {
  auto tok = Consume();

  // User-defined type cast: type_name'(expr) (§6.19.4, §6.24)
  bool is_cast =
      known_types_.count(tok.text) != 0 && Check(TokenKind::kApostrophe);
  if (is_cast) {
    auto saved = lexer_.SavePos();
    Consume();  // '
    if (Check(TokenKind::kLParen)) {
      Consume();  // (
      auto* cast = arena_.Create<Expr>();
      cast->kind = ExprKind::kCast;
      cast->text = tok.text;
      cast->range.start = tok.loc;
      cast->lhs = ParseExpr();
      Expect(TokenKind::kRParen);
      return cast;
    }
    lexer_.RestorePos(saved);
  }

  Expr* result = ParseMemberAccessChain(tok);

  // Postfix chain: calls, selects, and member access (§8.22 arr[0].method())
  while (Check(TokenKind::kLParen) || Check(TokenKind::kLBracket)) {
    if (Check(TokenKind::kLParen)) {
      result = ParseCallExpr(result);
    } else {
      result = ParseSelectExpr(result);
    }
    if (Check(TokenKind::kDot) || Check(TokenKind::kColonColon)) {
      result = MakeMemberAccess(result);
    }
  }

  // Postfix increment/decrement (§11.4.2)
  if (Check(TokenKind::kPlusPlus) || Check(TokenKind::kMinusMinus)) {
    auto op_tok = Consume();
    auto* post = arena_.Create<Expr>();
    post->kind = ExprKind::kPostfixUnary;
    post->op = op_tok.kind;
    post->lhs = result;
    post->range.start = result->range.start;
    return post;
  }

  return ParseWithClause(result);
}

Expr* Parser::ParseCallExpr(Expr* callee) {
  Expect(TokenKind::kLParen);
  auto* call = arena_.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = callee->text;
  call->lhs = callee;
  call->range.start = callee->range.start;
  if (!Check(TokenKind::kRParen)) {
    if (Check(TokenKind::kDot)) {
      // Named arguments: .name(expr), ...
      ParseNamedArg(call);
      while (Match(TokenKind::kComma)) {
        ParseNamedArg(call);
      }
    } else {
      call->args.push_back(ParseExpr());
      while (Match(TokenKind::kComma)) {
        call->args.push_back(ParseExpr());
      }
    }
  }
  Expect(TokenKind::kRParen);
  return call;
}

// Skip a brace-delimited constraint block: { ... }
static void SkipConstraintBlock(Lexer& lexer) {
  int depth = 1;
  while (depth > 0 && !lexer.Peek().Is(TokenKind::kEof)) {
    if (lexer.Peek().Is(TokenKind::kLBrace)) ++depth;
    if (lexer.Peek().Is(TokenKind::kRBrace)) --depth;
    if (depth > 0) lexer.Next();
  }
  if (lexer.Peek().Is(TokenKind::kRBrace)) lexer.Next();
}

Expr* Parser::ParseWithClause(Expr* expr) {
  if (!Match(TokenKind::kKwWith)) return expr;
  // §18.7: randomize() with { constraint_block }
  if (Check(TokenKind::kLBrace)) {
    Consume();
    SkipConstraintBlock(lexer_);
    return expr;
  }
  Expect(TokenKind::kLParen);
  expr->with_expr = ParseExpr();
  Expect(TokenKind::kRParen);
  // §18.7: randomize() with (id_list) { constraint_block }
  if (Check(TokenKind::kLBrace)) {
    Consume();
    SkipConstraintBlock(lexer_);
  }
  return expr;
}

Expr* Parser::ParseSelectExpr(Expr* base) {
  Consume();  // LBracket
  auto* sel = arena_.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = base;
  sel->index = ParseExpr();
  if (Match(TokenKind::kPlusColon)) {
    sel->is_part_select_plus = true;
    sel->index_end = ParseExpr();
  } else if (Match(TokenKind::kMinusColon)) {
    sel->is_part_select_minus = true;
    sel->index_end = ParseExpr();
  } else if (Match(TokenKind::kColon)) {
    sel->index_end = ParseExpr();
  }
  Expect(TokenKind::kRBracket);
  return sel;
}

Expr* Parser::ParseSystemCall() {
  auto tok = Consume();
  auto* call = arena_.Create<Expr>();
  call->kind = ExprKind::kSystemCall;
  call->callee = tok.text;
  call->range.start = tok.loc;
  if (!Match(TokenKind::kLParen)) return call;
  if (!Check(TokenKind::kRParen)) {
    // §20.2/§21.2: system tasks allow empty arguments (,,)
    if (Check(TokenKind::kComma)) {
      call->args.push_back(nullptr);
    } else {
      call->args.push_back(ParseExpr());
    }
    while (Match(TokenKind::kComma)) {
      if (Check(TokenKind::kComma) || Check(TokenKind::kRParen)) {
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

  // Streaming concatenation: {<< ...} or {>> ...}
  if (Check(TokenKind::kLtLt) || Check(TokenKind::kGtGt)) {
    auto dir = CurrentToken().kind;
    auto* sc = ParseStreamingConcat(dir);
    Expect(TokenKind::kRBrace);
    return sc;
  }

  auto* first = ParseExpr();

  // Replication: {count{elements}}
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
  // §11.4.12: postfix bit-select/part-select on concatenation: {b,c}[5:2]
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
    case TokenKind::kKwString:
      return true;
    default:
      return false;
  }
}

Expr* Parser::ParsePatternReplication(Expr* count, SourceLoc loc) {
  Consume();  // '{'
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
  // §12.6: .variable_identifier is a pattern binding
  if (Check(TokenKind::kDot)) {
    auto loc = CurrentLoc();
    Consume();
    auto name = ExpectIdentifier();
    auto* id = arena_.Create<Expr>();
    id->kind = ExprKind::kIdentifier;
    id->text = name.text;
    id->range.start = loc;
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
  id->kind = ExprKind::kIdentifier;
  id->text = first.text;
  id->range.start = first.loc;
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

  // Replication form: '{count{expr, ...}}
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
    // §12.6: .variable_identifier is a pattern binding
    if (Check(TokenKind::kDot)) {
      Consume();
      auto name = ExpectIdentifier();
      auto* id = arena_.Create<Expr>();
      id->kind = ExprKind::kIdentifier;
      id->text = name.text;
      id->range.start = name.loc;
      pat->elements.push_back(id);
    } else {
      pat->elements.push_back(ParseExpr());
    }
  }

  Expect(TokenKind::kRBrace);
  return pat;
}

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

// --- Min:Typ:Max expression (§11.11) ---

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

// --- Inside expression (§11.4.13) ---

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
  // Range syntax: [lo:hi]
  if (Check(TokenKind::kLBracket)) {
    Consume();
    auto* lo = ParseExpr();
    Expect(TokenKind::kColon);
    auto* hi = ParseExpr();
    Expect(TokenKind::kRBracket);
    auto* range = arena_.Create<Expr>();
    range->kind = ExprKind::kSelect;
    range->index = lo;
    range->index_end = hi;
    return range;
  }
  return ParseExpr();
}

// --- Streaming concatenation (§11.4.14) ---

Expr* Parser::ParseStreamingConcat(TokenKind dir) {
  auto loc = CurrentLoc();
  Consume();  // << or >>
  auto* sc = arena_.Create<Expr>();
  sc->kind = ExprKind::kStreamingConcat;
  sc->range.start = loc;
  sc->op = dir;  // store direction

  // Optional slice_size: type keyword (byte, int, etc.) or expression.
  if (!Check(TokenKind::kLBrace)) {
    auto saved = lexer_.SavePos();
    auto tok = Consume();
    if (Check(TokenKind::kLBrace)) {
      // Single token followed by '{' — treat as type-sized slice.
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

// --- Named argument (§13.5.4) ---

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

// --- Compound assignment expression (§11.4.1) ---

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

// --- Parenthesized expression ---

static bool IsAssignOp(TokenKind kind) {
  switch (kind) {
    case TokenKind::kEq:
    case TokenKind::kPlusEq:
    case TokenKind::kMinusEq:
    case TokenKind::kStarEq:
    case TokenKind::kSlashEq:
    case TokenKind::kPercentEq:
    case TokenKind::kAmpEq:
    case TokenKind::kPipeEq:
    case TokenKind::kCaretEq:
    case TokenKind::kLtLtEq:
    case TokenKind::kGtGtEq:
    case TokenKind::kLtLtLtEq:
    case TokenKind::kGtGtGtEq:
      return true;
    default:
      return false;
  }
}

Expr* Parser::ParseParenExpr() {
  Consume();  // (
  auto* lhs = ParseExpr();
  // Assignment expression inside parens: (a = b), (a += 1)
  if (IsAssignOp(CurrentToken().kind)) {
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
  return lhs;
}

}  // namespace delta
