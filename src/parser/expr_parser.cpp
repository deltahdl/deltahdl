#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <format>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/expr_parser_internal.h"
#include "parser/operator_binding_power.h"
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

static bool IsIntegerAtomType(TokenKind kind) {
  static constexpr std::array kIntegerAtomTypes = {
      TokenKind::kKwByte,    TokenKind::kKwShortint, TokenKind::kKwInt,
      TokenKind::kKwLongint, TokenKind::kKwInteger,  TokenKind::kKwTime};
  return std::ranges::find(kIntegerAtomTypes, kind) != kIntegerAtomTypes.end();
}

static int LiteralDigitValue(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}

static uint64_t FoldDigitsModulo64(std::string_view digits, uint64_t base) {
  uint64_t val = 0;
  for (char c : digits) {
    int d = LiteralDigitValue(c);
    if (d < 0 || static_cast<uint64_t>(d) >= base) break;
    val = val * base + static_cast<uint64_t>(d);
  }
  return val;
}

uint64_t ParseIntText(std::string_view text) {
  std::string buf = LiteralTextWithoutSeparators(text);

  auto tick = buf.find('\'');
  if (tick == std::string::npos) return FoldDigitsModulo64(buf, 10);

  size_t i = tick + 1;
  if (i < buf.size() && (buf[i] == 's' || buf[i] == 'S')) ++i;
  uint64_t base = 10;
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
  return FoldDigitsModulo64(std::string_view(buf).substr(i), base);
}

Expr* Parser::ParseExpr() {
  Expr* e = ParseExprBp(0);
  ReportPredicateOperator(e, diag_);
  if (WithOpensRange(lexer_)) ParseWithClauseRange(false);
  return e;
}

Expr* Parser::ParseExprBp(int min_bp) {
  auto* lhs = ParsePrefixExpr();
  return ParseInfixBp(lhs, min_bp);
}

static Expr* MakePredicateNode(Arena& arena, TokenKind op, Expr* lhs) {
  auto* bin = arena.Create<Expr>();
  bin->kind = ExprKind::kBinary;
  bin->op = op;
  bin->range.start = lhs->range.start;
  bin->lhs = lhs;
  return bin;
}

Expr* Parser::TryParseSpecialInfix(Expr*& lhs, const Token& tok, int min_bp) {
  if (ReportUnaryOperatorAfterOperand(tok, diag_)) {
    Consume();
    if (!EndsExpression(CurrentToken())) ParseExprBp(min_bp);
    return lhs;
  }
  if (tok.kind == TokenKind::kQuestion && min_bp <= 1) {
    Consume();
    std::vector<Attribute> attrs = ParseAttributes();
    auto* tern = arena_.Create<Expr>();
    tern->kind = ExprKind::kTernary;
    tern->attrs = std::move(attrs);
    tern->range.start = lhs->range.start;
    tern->condition = lhs;
    tern->true_expr = ParseExpr();
    Expect(TokenKind::kColon, Subclause("11.4.11"));
    tern->false_expr =
        ParseExprBp(InfixBindingPower(TokenKind::kPipePipe).first);
    if (Check(TokenKind::kQuestion))
      tern->false_expr =
          TryParseSpecialInfix(tern->false_expr, CurrentToken(), 0);
    return tern;
  }

  if (tok.kind == TokenKind::kAmpAmpAmp && min_bp <= 0) {
    Consume();
    auto* bin = MakePredicateNode(arena_, TokenKind::kAmpAmpAmp, lhs);
    int depth = std::exchange(pattern_depth_, 0);
    bin->rhs = ParseExprBp(2);
    if (Check(TokenKind::kKwMatches)) {
      bin->rhs = TryParseSpecialInfix(bin->rhs, CurrentToken(), 0);
    }
    pattern_depth_ = depth;
    return bin;
  }

  if (tok.kind == TokenKind::kKwInside && min_bp <= 15) {
    return ParseInsideExpr(lhs);
  }

  if (tok.kind == TokenKind::kKwMatches && min_bp <= 0) {
    Consume();
    auto* bin = MakePredicateNode(arena_, TokenKind::kKwMatches, lhs);
    ++pattern_depth_;
    bin->rhs = ParseExprBp(2);
    --pattern_depth_;
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

    auto [lbp, rbp] = InfixBindingPower(tok.kind);
    if (lbp < 0 || lbp < min_bp) break;
    if (in_sequence_body_ && (tok.kind == TokenKind::kPipeDashGt ||
                              tok.kind == TokenKind::kPipeEqGt)) {
      break;
    }

    auto op = Consume();
    std::vector<Attribute> attrs = ParseAttributes();
    auto* rhs = ParseExprBp(rbp);
    auto* bin = arena_.Create<Expr>();
    bin->kind = ExprKind::kBinary;
    bin->attrs = std::move(attrs);
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
    std::vector<Attribute> attrs = ParseAttributes();
    auto* operand = ParsePrimaryExpr();
    CheckIncDecOperand(operand, diag_);
    auto* unary = arena_.Create<Expr>();
    unary->kind = ExprKind::kUnary;
    unary->attrs = std::move(attrs);
    unary->op = op.kind;
    unary->lhs = operand;
    unary->range.start = op.loc;
    return unary;
  }

  int bp = PrefixBindingPower(tok.kind);
  if (bp >= 0) {
    auto op = Consume();
    std::vector<Attribute> attrs = ParseAttributes();
    auto* operand = ParseExprBp(bp);
    auto* unary = arena_.Create<Expr>();
    unary->kind = ExprKind::kUnary;
    unary->attrs = std::move(attrs);
    unary->op = op.kind;
    unary->lhs = operand;
    unary->range.start = op.loc;
    return unary;
  }
  return ParsePrimaryExpr();
}

Expr* Parser::ParseNewExpr() {
  auto* expr = arena_.Create<Expr>();
  expr->kind = ExprKind::kCall;
  expr->text = "new";
  expr->range.start = Consume().loc;
  if (Check(TokenKind::kLBracket)) {
    Consume();
    expr->args.push_back(ParseExpr());
    Expect(TokenKind::kRBracket, Subclause("7.5.1"));
    if (Check(TokenKind::kLParen)) {
      auto open = CurrentLoc();
      ParseParenList(expr->args);
      if (expr->args.size() != 2) {
        diag_.Error(open,
                    "a dynamic array's new takes one expression in its "
                    "parentheses, the array whose elements it starts with",
                    Subclause("A.2.4"));
      }
    }
  } else if (Check(TokenKind::kLParen)) {
    ParseListOfArguments(expr);
  }

  if (StartsShallowCopySource()) expr->lhs = ParseExpr();
  return expr;
}

static bool EndsTaggedMember(TokenKind kind) {
  static constexpr std::array kEnds = {
      TokenKind::kSemicolon, TokenKind::kComma,   TokenKind::kRParen,
      TokenKind::kRBrace,    TokenKind::kColon,   TokenKind::kEof,
      TokenKind::kAmpAmpAmp, TokenKind::kQuestion};
  return std::ranges::find(kEnds, kind) != kEnds.end();
}

Expr* Parser::ParseTaggedExpr() {
  auto* expr = arena_.Create<Expr>();
  expr->kind = ExprKind::kTagged;
  expr->range.start = Consume().loc;
  auto mt = ExpectIdentifier(Subclause("7.3.2"));
  expr->rhs = arena_.Create<Expr>();
  expr->rhs->kind = ExprKind::kIdentifier;
  expr->rhs->text = mt.text;
  expr->rhs->range.start = mt.loc;
  if (Check(TokenKind::kLParen)) {
    Consume();
    expr->lhs = ParseExpr();
    Expect(TokenKind::kRParen, Subclause("7.3.2"));
  } else if (Check(TokenKind::kApostropheLBrace)) {
    expr->lhs = ParseAssignmentPattern();
  } else if (Check(TokenKind::kDot)) {
    expr->lhs = ParsePrimaryExpr();
  } else if (!EndsTaggedMember(CurrentToken().kind)) {
    if (pattern_depth_ > 0) {
      expr->lhs = ParseExprBp(2);
    } else if (InfixBindingPower(CurrentToken().kind).first < 0) {
      expr->lhs = ParsePrimaryExpr();
    }
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
        diag_.Error(e->rhs->range.start, "'super.super' is not allowed",
                    Subclause("8.15"));
        break;
      }
    }
  }
  return ParseNameTail(result);
}

Expr* MakeNodeCast(Arena& arena, Expr* type_node, Expr* value) {
  auto* cast = arena.Create<Expr>();
  cast->kind = ExprKind::kCast;
  cast->range.start = type_node->range.start;
  cast->rhs = type_node;
  cast->lhs = value;
  return cast;
}

Expr* MakeIdentifierNode(Arena& arena, std::string_view text, SourceLoc loc) {
  auto* id = arena.Create<Expr>();
  id->kind = ExprKind::kIdentifier;
  id->text = text;
  id->range.start = loc;
  return id;
}

Expr* MakeTextCast(Arena& arena, std::string_view type_text, SourceLoc start,
                   Expr* value) {
  auto* cast = arena.Create<Expr>();
  cast->kind = ExprKind::kCast;
  cast->text = type_text;
  cast->range.start = start;
  cast->lhs = value;
  return cast;
}

Expr* MakePostfixUnary(Arena& arena, TokenKind op, Expr* operand) {
  auto* post = arena.Create<Expr>();
  post->kind = ExprKind::kPostfixUnary;
  post->op = op;
  post->lhs = operand;
  post->range.start = operand->range.start;
  return post;
}

namespace {

Expr* MakeErrorExpr(Arena& arena, SourceLoc loc) {
  auto* err = arena.Create<Expr>();
  err->kind = ExprKind::kIntegerLiteral;
  err->range.start = loc;
  return err;
}

}  // namespace

Expr* Parser::ParseTypeRefPrimary() {
  auto* ref = ParseTypeRefExpr();
  if (Check(TokenKind::kApostropheLBrace)) {
    auto* pat = ParseAssignmentPattern();
    return ParseMethodTail(MakeNodeCast(arena_, ref, pat));
  }
  if (Match(TokenKind::kApostrophe)) {
    Expect(TokenKind::kLParen, Subclause("6.24.1"));
    auto* cast = MakeNodeCast(arena_, ref, ParseExpr());
    Expect(TokenKind::kRParen, Subclause("6.24.1"));
    return ParseMethodTail(cast);
  }
  return ref;
}

Expr* Parser::ParsePrimaryExpr() {
  auto tok = CurrentToken();

  switch (tok.kind) {
    case TokenKind::kIntLiteral:
      return ParseMethodTail(ParseIntLiteralPrimary(tok));
    case TokenKind::kUnbasedUnsizedLiteral:
      return ParseMethodTail(
          MakeLiteral(ExprKind::kUnbasedUnsizedLiteral, tok));
    case TokenKind::kRealLiteral:
      return ParseMethodTail(MakeLiteral(ExprKind::kRealLiteral, tok));
    case TokenKind::kTimeLiteral:
      return ParseMethodTail(MakeLiteral(ExprKind::kTimeLiteral, tok));
    case TokenKind::kStringLiteral:
      return ParseMethodTail(MakeLiteral(ExprKind::kStringLiteral, tok));
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
      return ParseMethodTail(ParseAssignmentPattern());
    case TokenKind::kKwType:
      return ParseTypeRefPrimary();
    case TokenKind::kDollar:
    case TokenKind::kKwNull:
      return ParseMethodTail(MakeLiteral(ExprKind::kIdentifier, tok));
    case TokenKind::kKwThis:
    case TokenKind::kKwSuper:
      return ParseThisOrSuperExpr();
    case TokenKind::kKwLocal:
      return ParseLocalScopeExpr();
    case TokenKind::kKwTagged:
      return ParseTaggedExpr();
    case TokenKind::kKwNew:
      return ParseNewExpr();

    case TokenKind::kDotStar:
    case TokenKind::kDot:
      return ParseDotPattern();
    default:
      break;
  }

  if (IsCastTypeToken(tok.kind)) return ParseCastOrTypedPattern();

  diag_.Error(tok.loc, "expected expression", Subclause("11.2"));
  Consume();
  return MakeErrorExpr(arena_, tok.loc);
}

Expr* Parser::ParseCastOrTypedPattern() {
  auto saved = lexer_.SavePos();
  auto type_tok = Consume();

  if (Check(TokenKind::kApostropheLBrace)) {
    if (!IsIntegerAtomType(type_tok.kind)) {
      diag_.Error(type_tok.loc,
                  std::format("'{}' cannot prefix an assignment pattern",
                              type_tok.text),
                  Subclause("10.9"));
    }
    auto* pat = ParseAssignmentPattern();
    return ParseMethodTail(
        MakeTextCast(arena_, type_tok.text, type_tok.loc, pat));
  }

  if (Check(TokenKind::kApostrophe)) {
    lexer_.RestorePos(saved);
    return ParseCastExpr();
  }

  auto* id = arena_.Create<Expr>();
  id->kind = ExprKind::kIdentifier;
  id->text = type_tok.text;
  id->range.start = type_tok.loc;

  while (AtSelectBracket()) id = ParseSelectExpr(id);
  return id;
}

static bool IsMethodKeyword(TokenKind kind) {
  switch (kind) {
    case TokenKind::kKwNew:
    case TokenKind::kKwUnique:
    case TokenKind::kKwAnd:
    case TokenKind::kKwOr:
    case TokenKind::kKwXor:
    case TokenKind::kKwSuper:
      return true;
    default:
      return false;
  }
}

Expr* Parser::MakeMemberAccess(Expr* base) {
  bool is_scope = CurrentToken().kind == TokenKind::kColonColon;
  Consume();
  auto member_tok =
      IsMethodKeyword(CurrentToken().kind) ||
              (is_scope && Check(TokenKind::kKwThis))
          ? Consume()
          : ExpectIdentifier(Subclause(is_scope ? "23.7.1" : "23.7"));
  if (is_scope && member_tok.kind == TokenKind::kKwNew &&
      StartsShallowCopySource()) {
    diag_.Error(CurrentLoc(),
                "a typed constructor call cannot take a shallow-copy source; "
                "drop the class scope to copy an object with 'new'",
                Subclause("8.12"));
    ParseExpr();
  }
  if (member_tok.text == "triggered" || member_tok.text == "matched") {
    RecordTriggeredRead(base);
  }
  auto* member_id = arena_.Create<Expr>();
  member_id->kind = ExprKind::kIdentifier;
  member_id->text = member_tok.text;
  member_id->range.start = member_tok.loc;
  auto* acc = arena_.Create<Expr>();
  acc->kind = ExprKind::kMemberAccess;
  acc->lhs = base;
  acc->rhs = member_id;
  acc->is_scope_resolution = is_scope;
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

Expr* Parser::TryParseUserTypeCast(const Token& tok) {
  if (known_types_.count(tok.text) == 0) return nullptr;

  if (Check(TokenKind::kApostropheLBrace)) {
    auto* pat = ParseAssignmentPattern();
    return ParseMethodTail(MakeTextCast(arena_, tok.text, tok.loc, pat));
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
  Expect(TokenKind::kRParen, Subclause("6.24.1"));
  return ParseMethodTail(cast);
}

Expr* Parser::TryParseIdentifierCast(Expr* base, bool* handled) {
  *handled = true;
  if (Check(TokenKind::kApostropheLBrace)) {
    auto* pat = ParseAssignmentPattern();
    return ParseMethodTail(MakeNodeCast(arena_, base, pat));
  }
  if (Check(TokenKind::kApostrophe)) {
    auto saved = lexer_.SavePos();
    Consume();
    if (Check(TokenKind::kLParen)) {
      Consume();
      auto* value = ParseExpr();
      auto* cast = MakeNodeCast(arena_, base, value);
      Expect(TokenKind::kRParen, Subclause("6.24.1"));
      return ParseMethodTail(cast);
    }
    lexer_.RestorePos(saved);
  }
  *handled = false;
  return base;
}

static void ReportBracketAfterLastSelect(const Expr* base, SourceLoc loc,
                                         DiagEngine& diag) {
  if (base->kind != ExprKind::kSelect) return;
  if (base->index_end != nullptr) {
    diag.Error(loc, "a part-select ends a select; no bracket follows it",
               Subclause("A.8.4"));
  } else if (base->base->kind == ExprKind::kCall ||
             base->base->kind == ExprKind::kSystemCall) {
    diag.Error(loc,
               "a subroutine call's result takes one select; this is a second",
               Subclause("A.8.4"));
  }
}

Expr* Parser::ParseIdentifierPostfixChain(Expr* result) {
  while (Check(TokenKind::kLParen) || AtSelectBracket() ||
         Check(TokenKind::kAttrStart)) {
    if (Check(TokenKind::kAttrStart)) {
      ParseAttributes();
      continue;
    }
    if (Check(TokenKind::kLParen)) {
      result = ParseCallExpr(result);
    } else {
      ReportBracketAfterLastSelect(result, CurrentLoc(), diag_);
      result = ParseSelectExpr(result);
    }
    while (Check(TokenKind::kDot) || Check(TokenKind::kColonColon)) {
      result = MakeMemberAccess(result);
    }
  }
  return result;
}

Expr* Parser::ParseWithClauseTail(Expr* result) {
  while (Check(TokenKind::kDot) || AtSelectBracket()) {
    if (Check(TokenKind::kDot)) {
      result = ParseMethodTail(result);
    } else {
      ReportBracketAfterLastSelect(result, CurrentLoc(), diag_);
      result = ParseSelectExpr(result);
    }
  }
  return result;
}

void ReportLocalQualifier(SourceLoc loc, DiagEngine& diag) {
  diag.Error(loc,
             "the 'local::' qualifier stands only in an inline constraint "
             "block",
             Subclause("A.8.4"));
}

Expr* Parser::ParseLocalScopeExpr() {
  auto tok = Consume();
  if (!Check(TokenKind::kColonColon)) {
    diag_.Error(tok.loc, "'local' may only appear here as a 'local::' prefix",
                Subclause("18.7.1"));
    return MakeErrorExpr(arena_, tok.loc);
  }
  if (constraint_block_depth_ == 0) ReportLocalQualifier(tok.loc, diag_);
  Expr* result = ParseMemberAccessChain(tok);
  bool cast_handled = false;
  Expr* cast = TryParseIdentifierCast(result, &cast_handled);
  if (cast_handled) return cast;
  return ParseIdentifierPostfixChain(result);
}

Expr* Parser::ParseIdentifierExpr() {
  auto tok = Consume();

  if (auto* cast = TryParseUserTypeCast(tok)) return cast;

  Expr* result = ParseMemberAccessChain(tok);

  if (Check(TokenKind::kHash)) {
    auto saved = lexer_.SavePos();
    Consume();
    bool is_param_value = Check(TokenKind::kLParen);
    lexer_.RestorePos(saved);
    if (is_param_value) result = ParseParameterizedScope(result);
  }

  bool cast_handled = false;
  Expr* cast = TryParseIdentifierCast(result, &cast_handled);
  if (cast_handled) return cast;

  return ParseNameTail(result);
}

namespace {

bool IsSuperNewCallee(const Expr* callee) {
  return callee != nullptr && callee->kind == ExprKind::kMemberAccess &&
         callee->lhs->text == "super" && callee->rhs->text == "new";
}

}  // namespace

void Parser::ParseCallArgs(Expr* call) {
  if (Check(TokenKind::kKwDefault)) {
    auto tok = Consume();
    if (!IsSuperNewCallee(call->lhs)) {
      diag_.Error(tok.loc,
                  "'default' stands in place of an argument list only in a "
                  "constructor's super.new call",
                  Subclause("A.8.2"));
    }
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
  if (callee->kind == ExprKind::kCall || callee->kind == ExprKind::kSelect) {
    diag_.Error(CurrentLoc(),
                "an argument list follows the name of a subroutine or a "
                "method, not a call or a select",
                Subclause("A.8.2"));
  }
  auto* call = arena_.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = callee->text;
  call->lhs = callee;
  call->range.start = callee->range.start;
  ParseListOfArguments(call);
  CheckRandomizeArgList(call);
  return call;
}

ClassMember* Parser::CaptureInlineConstraintBlock() {
  auto* block = arena_.Create<ClassMember>();
  block->kind = ClassMemberKind::kConstraint;
  ScanConstraintBodyRelations(block, true);
  return block;
}

bool Parser::AtSelectBracket() {
  if (!Check(TokenKind::kLBracket)) return false;
  if (!in_sequence_body_) return true;
  auto saved = lexer_.SavePos();
  Consume();
  bool repetition = Check(TokenKind::kStar) || Check(TokenKind::kArrow) ||
                    Check(TokenKind::kEq) || Check(TokenKind::kPlus);
  lexer_.RestorePos(saved);
  return !repetition;
}

Expr* Parser::ParseSelectExpr(Expr* base) {
  Consume();
  auto* sel = arena_.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = base;
  sel->range.start = base->range.start;
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
  Expect(TokenKind::kRBracket, Subclause("11.5.1"));
  return sel;
}

}  // namespace delta
