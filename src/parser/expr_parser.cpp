#include <charconv>
#include <cmath>
#include <cstdlib>

#include "parser/expr_parser_internal.h"
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
    case TokenKind::kKwRealtime:
    case TokenKind::kKwTime:
    case TokenKind::kKwReg:
    case TokenKind::kKwSigned:
    case TokenKind::kKwUnsigned:
    case TokenKind::kKwString:
    case TokenKind::kKwConst:
    case TokenKind::kKwVoid:
      return true;
    default:
      return false;
  }
}

uint64_t ParseIntText(std::string_view text) {
  std::string buf;
  buf.reserve(text.size());
  for (char c : text) {
    if (c != '_' && c != ' ' && c != '\t') buf.push_back(c);
  }

  auto tick = buf.find('\'');
  if (tick == std::string::npos) {
    uint64_t val = 0;
    std::from_chars(buf.data(), buf.data() + buf.size(), val, 10);
    return val;
  }

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

static uint32_t ExtractLiteralSize(std::string_view text) {
  auto tick = text.find('\'');
  if (tick == std::string_view::npos || tick == 0) return 0;
  uint64_t size = 0;
  for (size_t i = 0; i < tick; ++i) {
    char c = text[i];
    if (c == '_' || c == ' ' || c == '\t') continue;
    if (c < '0' || c > '9') return 0;
    size = size * 10 + (c - '0');
  }
  return static_cast<uint32_t>(size);
}

static bool HasXZDigits(std::string_view text) {
  auto tick = text.find('\'');
  if (tick == std::string_view::npos) return false;
  for (size_t i = tick + 1; i < text.size(); ++i) {
    char c = text[i];
    if (c == 'x' || c == 'X' || c == 'z' || c == 'Z' || c == '?') return true;
  }
  return false;
}

static double ParseRealText(std::string_view text) {
  std::string buf;
  buf.reserve(text.size());
  for (char c : text) {
    if (c != '_') buf.push_back(c);
  }
  return std::strtod(buf.c_str(), nullptr);
}

// Scales a time-literal's real value from the unit named by its suffix into the
// enclosing module's time unit (defaulting to ns when no module is active).
static double ScaleTimeLiteral(double real_val, std::string_view text,
                               TimeUnit current_unit) {
  TimeUnit literal_unit = TimeUnit::kNs;
  auto t = text;
  if (t.size() < 2 || !ParseTimeUnitStr(t.substr(t.size() - 2), literal_unit)) {
    if (!t.empty()) {
      ParseTimeUnitStr(t.substr(t.size() - 1), literal_unit);
    }
  }
  int exp = static_cast<int>(literal_unit) - static_cast<int>(current_unit);
  if (exp != 0) {
    real_val *= std::pow(10.0, exp);
  }
  return real_val;
}

static std::pair<int, int> InfixBp(TokenKind kind) {
  switch (kind) {
    case TokenKind::kPipeDashGt:
    case TokenKind::kPipeEqGt:
      return {1, 2};
    case TokenKind::kArrow:
    case TokenKind::kLtDashGt:
      return {2, 1};
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
      return {23, 24};
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

Expr* Parser::TryParseSpecialInfix(Expr*& lhs, const Token& tok, int min_bp) {
  if (tok.kind == TokenKind::kQuestion && min_bp <= 1) {
    Consume();
    ParseAttributes();
    auto* tern = arena_.Create<Expr>();
    tern->kind = ExprKind::kTernary;
    tern->condition = lhs;
    tern->true_expr = ParseExprBp(0);
    Expect(TokenKind::kColon);
    tern->false_expr = ParseExprBp(0);
    return tern;
  }

  if (tok.kind == TokenKind::kAmpAmpAmp && min_bp <= 0) {
    Consume();
    auto* bin = arena_.Create<Expr>();
    bin->kind = ExprKind::kBinary;
    bin->op = TokenKind::kAmpAmpAmp;
    bin->lhs = lhs;
    bin->rhs = ParseExprBp(1);
    return bin;
  }

  if (tok.kind == TokenKind::kKwInside && min_bp <= 15) {
    return ParseInsideExpr(lhs);
  }

  if (tok.kind == TokenKind::kKwMatches && min_bp <= 1) {
    Consume();
    auto* bin = arena_.Create<Expr>();
    bin->kind = ExprKind::kBinary;
    bin->op = TokenKind::kKwMatches;
    bin->lhs = lhs;
    bin->rhs = ParseExprBp(2);
    return bin;
  }
  return nullptr;
}

Expr* Parser::ParseInfixBp(Expr* lhs, int min_bp) {
  while (true) {
    auto tok = CurrentToken();
    if (tok.IsEof()) break;

    auto* special = TryParseSpecialInfix(lhs, tok, min_bp);
    if (special) {
      lhs = special;
      continue;
    }

    auto [lbp, rbp] = InfixBp(tok.kind);
    if (lbp < 0 || lbp < min_bp) break;

    auto op = Consume();
    ParseAttributes();
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
    WarnSizedOverflow(tok);
  } else if (kind == ExprKind::kUnbasedUnsizedLiteral) {
    if (tok.text.size() >= 2 && tok.text[1] == '1') {
      lit->int_val = ~uint64_t{0};
    }
  } else if (kind == ExprKind::kRealLiteral || kind == ExprKind::kTimeLiteral) {
    lit->real_val = ParseRealText(tok.text);
    if (kind == ExprKind::kTimeLiteral) {
      TimeUnit current_unit =
          current_module_ ? current_module_->time_unit : TimeUnit::kNs;
      lit->real_val = ScaleTimeLiteral(lit->real_val, tok.text, current_unit);
    }
  }
  return lit;
}

void Parser::WarnSizedOverflow(const Token& tok) {
  uint32_t size = ExtractLiteralSize(tok.text);
  if (size == 0) {
    auto tick = tok.text.find('\'');
    if (tick != std::string_view::npos && tick > 0) {
      diag_.Error(tok.loc, "size of integer literal shall be nonzero");
    }
    return;
  }
  if (size >= 64) return;
  if (HasXZDigits(tok.text)) return;
  uint64_t val = ParseIntText(tok.text);
  if (val >= (1ULL << size)) {
    diag_.Warning(tok.loc, "value exceeds size of literal");
  }
}

Expr* Parser::ParseNewExpr() {
  auto* expr = arena_.Create<Expr>();
  expr->kind = ExprKind::kCall;
  expr->text = "new";
  expr->range.start = Consume().loc;
  if (Check(TokenKind::kLBracket)) {
    Consume();
    expr->args.push_back(ParseExpr());
    Expect(TokenKind::kRBracket);
    if (Check(TokenKind::kLParen)) ParseParenList(expr->args);
  } else if (Check(TokenKind::kLParen)) {
    ParseParenList(expr->args);
  }

  if (CheckIdentifier()) expr->lhs = ParseExpr();
  return expr;
}

Expr* Parser::ParseTaggedExpr() {
  auto* expr = arena_.Create<Expr>();
  expr->kind = ExprKind::kTagged;
  expr->range.start = Consume().loc;
  auto mt = ExpectIdentifier();
  expr->rhs = arena_.Create<Expr>();
  expr->rhs->kind = ExprKind::kIdentifier;
  expr->rhs->text = mt.text;
  expr->rhs->range.start = mt.loc;
  if (Check(TokenKind::kLParen)) {
    Consume();
    expr->lhs = ParseExpr();
    Expect(TokenKind::kRParen);
  } else if (Check(TokenKind::kApostropheLBrace)) {
    expr->lhs = ParseAssignmentPattern();
  } else if (Check(TokenKind::kDot)) {
    expr->lhs = ParsePrimaryExpr();
  } else if (!Check(TokenKind::kSemicolon) && !Check(TokenKind::kComma) &&
             !Check(TokenKind::kRParen) && !Check(TokenKind::kRBrace) &&
             !Check(TokenKind::kColon) && !Check(TokenKind::kEof) &&
             !Check(TokenKind::kAmpAmpAmp)) {
    expr->lhs = ParseExpr();
  }
  return expr;
}

Expr* Parser::ParseThisOrSuperExpr() {
  auto super_tok = Consume();
  Expr* result = ParseMemberAccessChain(super_tok);

  if (super_tok.kind == TokenKind::kKwSuper) {
    for (auto* e = result; e && e->kind == ExprKind::kMemberAccess;
         e = e->lhs) {
      if (e->rhs && e->rhs->kind == ExprKind::kIdentifier &&
          e->rhs->text == "super") {
        diag_.Error(e->rhs->range.start, "'super.super' is not allowed");
        break;
      }
    }
  }
  if (Check(TokenKind::kLParen)) result = ParseCallExpr(result);
  if (Check(TokenKind::kLBracket)) result = ParseSelectExpr(result);
  return ParseWithClause(result);
}

namespace {

// Builds a width/type cast whose target type is carried by an AST node
// (cast->rhs) and whose value is carried by cast->lhs. The cast inherits the
// type node's start location. Pure node construction; the caller has already
// parsed both operands.
Expr* MakeNodeCast(Arena& arena, Expr* type_node, Expr* value) {
  auto* cast = arena.Create<Expr>();
  cast->kind = ExprKind::kCast;
  cast->range.start = type_node->range.start;
  cast->rhs = type_node;
  cast->lhs = value;
  return cast;
}

// Builds a cast whose target type is carried by a name string (cast->text) and
// whose value is carried by cast->lhs, starting at the given location. Pure
// node construction.
Expr* MakeTextCast(Arena& arena, std::string_view type_text, SourceLoc start,
                   Expr* value) {
  auto* cast = arena.Create<Expr>();
  cast->kind = ExprKind::kCast;
  cast->text = type_text;
  cast->range.start = start;
  cast->lhs = value;
  return cast;
}

// Builds a bare identifier node carrying the given name text and location.
// Pure node construction.
Expr* MakeIdentifierNode(Arena& arena, std::string_view text, SourceLoc loc) {
  auto* id = arena.Create<Expr>();
  id->kind = ExprKind::kIdentifier;
  id->text = text;
  id->range.start = loc;
  return id;
}

// Builds a postfix increment/decrement node wrapping an already-parsed operand,
// using the already-consumed operator's kind. Pure node construction.
Expr* MakePostfixUnary(Arena& arena, TokenKind op, Expr* operand) {
  auto* post = arena.Create<Expr>();
  post->kind = ExprKind::kPostfixUnary;
  post->op = op;
  post->lhs = operand;
  post->range.start = operand->range.start;
  return post;
}

// Builds the placeholder integer-literal node returned after an "expected
// expression" diagnostic, so parsing can continue past the offending token.
// Pure node construction.
Expr* MakeErrorExpr(Arena& arena, SourceLoc loc) {
  auto* err = arena.Create<Expr>();
  err->kind = ExprKind::kIntegerLiteral;
  err->range.start = loc;
  return err;
}

}  // namespace

// casting_type allows constant_primary; an integer literal followed by '(expr)
// is a width-cast (the literal is the target width). Otherwise it is just the
// integer literal.
Expr* Parser::ParseIntLiteralPrimary(const Token& tok) {
  auto* lit = MakeLiteral(ExprKind::kIntegerLiteral, tok);
  if (!Check(TokenKind::kApostrophe)) return lit;
  auto saved = lexer_.SavePos();
  Consume();
  if (!Check(TokenKind::kLParen)) {
    lexer_.RestorePos(saved);
    return lit;
  }
  Consume();
  auto* value = ParseExpr();
  auto* cast = MakeNodeCast(arena_, lit, value);
  Expect(TokenKind::kRParen);
  return cast;
}

// type_reference primary ('type(...)' or the 'type' keyword), optionally used
// as the casting_type of an assignment-pattern cast.
Expr* Parser::ParseTypeRefPrimary() {
  auto* ref = ParseTypeRefExpr();
  if (Check(TokenKind::kApostropheLBrace)) {
    auto* pat = ParseAssignmentPattern();
    return MakeNodeCast(arena_, ref, pat);
  }
  return ref;
}

Expr* Parser::ParsePrimaryExpr() {
  auto tok = CurrentToken();

  switch (tok.kind) {
    case TokenKind::kIntLiteral:
      return ParseIntLiteralPrimary(tok);
    case TokenKind::kUnbasedUnsizedLiteral:
      return MakeLiteral(ExprKind::kUnbasedUnsizedLiteral, tok);
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
      return ParseTypeRefPrimary();
    case TokenKind::kDollar:
    case TokenKind::kKwNull:
      return MakeLiteral(ExprKind::kIdentifier, tok);
    case TokenKind::kKwThis:
    case TokenKind::kKwSuper:
      return ParseThisOrSuperExpr();
    case TokenKind::kKwTagged:
      return ParseTaggedExpr();
    case TokenKind::kKwNew:
      return ParseNewExpr();

    case TokenKind::kDotStar: {
      auto loc = Consume().loc;
      return MakeIdentifierNode(arena_, ".*", loc);
    }

    case TokenKind::kDot: {
      auto loc = Consume().loc;
      auto name = ExpectIdentifier();
      return MakeIdentifierNode(arena_, name.text, loc);
    }
    default:
      break;
  }

  if (IsCastTypeToken(tok.kind)) return ParseCastOrTypedPattern();

  diag_.Error(tok.loc, "expected expression");
  Consume();
  return MakeErrorExpr(arena_, tok.loc);
}

Expr* Parser::ParseCastOrTypedPattern() {
  auto saved = lexer_.SavePos();
  auto type_tok = Consume();

  if (Check(TokenKind::kApostropheLBrace)) {
    auto* pat = ParseAssignmentPattern();
    return MakeTextCast(arena_, type_tok.text, type_tok.loc, pat);
  }

  if (Check(TokenKind::kApostrophe)) {
    lexer_.RestorePos(saved);
    return ParseCastExpr();
  }

  auto* id = arena_.Create<Expr>();
  id->kind = ExprKind::kIdentifier;
  id->text = type_tok.text;
  id->range.start = type_tok.loc;

  if (Check(TokenKind::kLBracket)) return ParseSelectExpr(id);
  return id;
}

static bool IsMethodKeyword(TokenKind kind) {
  switch (kind) {
    case TokenKind::kKwNew:
    case TokenKind::kKwUnique:
    case TokenKind::kKwAnd:
    case TokenKind::kKwOr:
    case TokenKind::kKwXor:
      return true;
    default:
      return false;
  }
}

Expr* Parser::MakeMemberAccess(Expr* base) {
  Consume();
  auto member_tok =
      IsMethodKeyword(CurrentToken().kind) ? Consume() : ExpectIdentifier();
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

Expr* Parser::ParseParameterizedScope(Expr* base) {
  Consume();
  if (!Check(TokenKind::kLParen)) return base;
  base->has_param_spec = true;
  Consume();
  if (!Check(TokenKind::kRParen)) {
    base->elements.push_back(ParseExpr());
    while (Check(TokenKind::kComma)) {
      Consume();
      base->elements.push_back(ParseExpr());
    }
  }
  Expect(TokenKind::kRParen);
  while (Check(TokenKind::kDot) || Check(TokenKind::kColonColon)) {
    base = MakeMemberAccess(base);
  }
  return base;
}

Expr* Parser::TryParseUserTypeCast(const Token& tok) {
  if (known_types_.count(tok.text) == 0) return nullptr;

  if (Check(TokenKind::kApostropheLBrace)) {
    auto* pat = ParseAssignmentPattern();
    return MakeTextCast(arena_, tok.text, tok.loc, pat);
  }
  if (!Check(TokenKind::kApostrophe)) return nullptr;
  auto saved = lexer_.SavePos();
  Consume();
  if (!Check(TokenKind::kLParen)) {
    lexer_.RestorePos(saved);
    return nullptr;
  }
  Consume();
  auto* value = ParseExpr();
  auto* cast = MakeTextCast(arena_, tok.text, tok.loc, value);
  Expect(TokenKind::kRParen);
  return cast;
}

// An identifier or scoped name may be the casting_type of a cast: "id'{...}"
// (assignment-pattern cast) or "id'(expr)" (value cast). Returns the cast node
// when one is recognized, leaving *handled true; otherwise returns base with
// *handled false and the lexer position restored.
Expr* Parser::TryParseIdentifierCast(Expr* base, bool* handled) {
  *handled = true;
  if (Check(TokenKind::kApostropheLBrace)) {
    auto* pat = ParseAssignmentPattern();
    return MakeNodeCast(arena_, base, pat);
  }
  if (Check(TokenKind::kApostrophe)) {
    auto saved = lexer_.SavePos();
    Consume();
    if (Check(TokenKind::kLParen)) {
      Consume();
      auto* value = ParseExpr();
      auto* cast = MakeNodeCast(arena_, base, value);
      Expect(TokenKind::kRParen);
      return cast;
    }
    lexer_.RestorePos(saved);
  }
  *handled = false;
  return base;
}

// Parse the run of postfix call/select operators (with optional intervening
// attribute lists and trailing member accesses) that follow a name primary.
Expr* Parser::ParseIdentifierPostfixChain(Expr* result) {
  while (Check(TokenKind::kLParen) || Check(TokenKind::kLBracket) ||
         Check(TokenKind::kAttrStart)) {
    if (Check(TokenKind::kAttrStart)) {
      ParseAttributes();
      continue;
    }
    if (Check(TokenKind::kLParen)) {
      result = ParseCallExpr(result);
    } else {
      result = ParseSelectExpr(result);
    }
    if (Check(TokenKind::kDot) || Check(TokenKind::kColonColon)) {
      result = MakeMemberAccess(result);
    }
  }
  return result;
}

// Parse the member/select tail that may follow a 'with' clause expression.
Expr* Parser::ParseWithClauseTail(Expr* result) {
  while (Check(TokenKind::kDot) || Check(TokenKind::kLBracket)) {
    if (!Check(TokenKind::kDot)) {
      result = ParseSelectExpr(result);
      continue;
    }
    result = MakeMemberAccess(result);
    if (Check(TokenKind::kLParen)) result = ParseCallExpr(result);
  }
  return result;
}

Expr* Parser::ParseIdentifierExpr() {
  auto tok = Consume();

  if (auto* cast = TryParseUserTypeCast(tok)) return cast;

  Expr* result = ParseMemberAccessChain(tok);

  if (Check(TokenKind::kHash) && known_types_.count(tok.text) != 0) {
    result = ParseParameterizedScope(result);
  }

  bool cast_handled = false;
  Expr* cast = TryParseIdentifierCast(result, &cast_handled);
  if (cast_handled) return cast;

  result = ParseIdentifierPostfixChain(result);

  if (Check(TokenKind::kPlusPlus) || Check(TokenKind::kMinusMinus)) {
    auto op_tok = Consume();
    return MakePostfixUnary(arena_, op_tok.kind, result);
  }

  result = ParseWithClause(result);
  if (!result->with_expr) return result;

  return ParseWithClauseTail(result);
}

void Parser::ParseTrailingNamedArgs(Expr* call) {
  ParseNamedArg(call);
  while (Match(TokenKind::kComma)) {
    ParseNamedArg(call);
  }
}

void Parser::ParseCallArgs(Expr* call) {
  if (Check(TokenKind::kKwDefault)) {
    auto tok = Consume();
    auto* expr = arena_.Create<Expr>();
    expr->kind = ExprKind::kIdentifier;
    expr->text = tok.text;
    expr->range.start = tok.loc;
    call->args.push_back(expr);
    return;
  }
  if (Check(TokenKind::kComma) || Check(TokenKind::kRParen)) {
    call->args.push_back(nullptr);
  } else {
    call->args.push_back(ParseExpr());
  }
  while (Match(TokenKind::kComma)) {
    if (Check(TokenKind::kDot)) {
      ParseTrailingNamedArgs(call);
      break;
    }
    if (Check(TokenKind::kComma) || Check(TokenKind::kRParen)) {
      call->args.push_back(nullptr);
    } else {
      call->args.push_back(ParseExpr());
    }
  }
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
      ParseTrailingNamedArgs(call);
    } else {
      ParseCallArgs(call);
    }
  }
  Expect(TokenKind::kRParen);
  CheckRandomizeArgList(call);
  return call;
}

namespace {

// 18.11: a randomize() argument is one of the calling object's property names,
// possibly indexed or reached through a member access. It is a variable
// reference, never a computed expression.
bool IsPropertyNameArg(const Expr* arg) {
  switch (arg->kind) {
    case ExprKind::kIdentifier:
    case ExprKind::kMemberAccess:
    case ExprKind::kSelect:
      return true;
    default:
      return false;
  }
}

}  // namespace

void Parser::CheckRandomizeArgList(const Expr* call) {
  // 18.11: the inline random variable control list passed to randomize() is
  // limited to the names of properties of the calling object; expressions are
  // not allowed. Recognize the call either as a bare randomize(...) or as a
  // method call whose member name is randomize, then reject any argument that
  // is not a plain property reference. (A null argument, 18.11.1, is lexed as
  // an identifier and so is accepted here.)
  bool is_randomize =
      call->callee == "randomize" ||
      (call->lhs != nullptr && call->lhs->kind == ExprKind::kMemberAccess &&
       call->lhs->rhs != nullptr && call->lhs->rhs->text == "randomize");
  if (!is_randomize) return;
  for (const Expr* arg : call->args) {
    if (arg == nullptr) continue;
    if (IsPropertyNameArg(arg)) continue;
    diag_.Error(arg->range.start,
                "randomize() arguments shall be object property names, not "
                "expressions");
  }
}

Expr* Parser::ParseWithClause(Expr* expr) {
  if (!Match(TokenKind::kKwWith)) return expr;

  if (Check(TokenKind::kLBrace)) {
    Consume();
    SkipBraceBlock(lexer_);
    return expr;
  }

  if (Check(TokenKind::kLBracket)) {
    Consume();
    auto* range = arena_.Create<Expr>();
    range->kind = ExprKind::kSelect;
    range->index = ParseExpr();
    if (Match(TokenKind::kPlusColon)) {
      range->is_part_select_plus = true;
      range->index_end = ParseExpr();
    } else if (Match(TokenKind::kMinusColon)) {
      range->is_part_select_minus = true;
      range->index_end = ParseExpr();
    } else if (Match(TokenKind::kColon)) {
      range->index_end = ParseExpr();
    }
    expr->with_expr = range;
    Expect(TokenKind::kRBracket);
    return expr;
  }
  Expect(TokenKind::kLParen);
  expr->with_has_parens = true;
  if (!Check(TokenKind::kRParen)) {
    expr->with_expr = ParseExpr();
    // A.8.2 randomize_call's with-clause allows an identifier_list inside
    // the parentheses; array_manipulation_call's with-clause carries a
    // single expression. Tolerate either by consuming further entries.
    while (Match(TokenKind::kComma)) {
      ParseExpr();
    }
  }
  Expect(TokenKind::kRParen);

  if (Check(TokenKind::kLBrace)) {
    Consume();
    SkipBraceBlock(lexer_);
  }
  return expr;
}

Expr* Parser::ParseSelectExpr(Expr* base) {
  Consume();
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

}  // namespace delta
