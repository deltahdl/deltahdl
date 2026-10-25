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

// §10.9, Syntax 10-5: of the keywords IsCastTypeToken admits, only an
// integer_atom_type may prefix an assignment pattern; the other prefixes the
// grammar gives are names and type references, which are not keywords.
static bool IsIntegerAtomType(TokenKind kind) {
  static constexpr std::array kIntegerAtomTypes = {
      TokenKind::kKwByte,    TokenKind::kKwShortint, TokenKind::kKwInt,
      TokenKind::kKwLongint, TokenKind::kKwInteger,  TokenKind::kKwTime};
  return std::ranges::find(kIntegerAtomTypes, kind) != kIntegerAtomTypes.end();
}

// The value of one digit character of an integer literal, or -1 for a
// character that is no digit at all: an x, z or ? digit, which §5.7.1 sets to
// the unknown or high-impedance value rather than to a number.
static int LiteralDigitValue(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}

// Folds `digits` in `base` into 64 bits, wrapping modulo 2^64, so a literal
// wider than 64 bits yields its low 64 bits: the residue of each partial value
// is what the next digit multiplies, and unsigned overflow discards nothing
// below bit 64. The fold ends at the first character that is not a digit of
// the base -- an x, z or ? digit, or a digit above the base -- leaving what the
// digits before it made.
static uint64_t FoldDigitsModulo64(std::string_view digits, uint64_t base) {
  uint64_t val = 0;
  for (char c : digits) {
    int d = LiteralDigitValue(c);
    if (d < 0 || static_cast<uint64_t>(d) >= base) break;
    val = val * base + static_cast<uint64_t>(d);
  }
  return val;
}

// §5.7.1: a based literal's digits give its value in the base its base format
// names, and a simple decimal number gives its value in base 10; the size
// constant states the literal's exact width, so the digits can reach beyond
// the 64 bits Expr::int_val holds. int_val then holds the low 64 bits of the
// value, `96'h0123_4567_89AB_CDEF_0011_2233` giving 0x89ABCDEF00112233, which
// is what the elaborator's ConstEvalLiteral folds and what any 64-bit
// arithmetic on the value sees. The whole value is produced from the digits
// again where every bit is needed: EvalIntLiteral and SetDigitBits in
// src/simulator/evaluation_literal.cpp build the run-time vector, and
// SynthLower::LowerLiteralBit reads the digits for a bit at or above 64. An x,
// z or ? digit ends the fold, the digits before it standing; the same run-time
// reparse sets the bits such a digit covers.
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

// A.6.6 and A.8.3 give a cond_predicate, the clauses `&&&` joins with their
// `matches` patterns, two places: an if statement's condition, which
// Parser::ParseIfStmt reads through ParseExprBp, and a conditional operator's
// condition, which never stands as an expression of its own. A.8.6 makes
// neither operator a binary_operator, so one at the top of any other
// expression is reported. That covers one in parentheses, whose
// mintypmax_expression is an expression too. A.8.1 writes `with [
// array_range_expression ]` after the operand of a stream_expression alone,
// which Parser::ParseStreamingConcat reads short of this, so a range after
// any other expression is reported and read past.
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

// A cond_predicate's `&&&` or `matches` node over `lhs`, its right operand
// still to read. §12.4 and §12.6 write each as a left operand followed by the
// operator, which is where Parser::ParseInfixBp starts every other one.
static Expr* MakePredicateNode(Arena& arena, TokenKind op, Expr* lhs) {
  auto* bin = arena.Create<Expr>();
  bin->kind = ExprKind::kBinary;
  bin->op = op;
  bin->range.start = lhs->range.start;
  bin->lhs = lhs;
  return bin;
}

Expr* Parser::TryParseSpecialInfix(Expr*& lhs, const Token& tok, int min_bp) {
  if (tok.kind == TokenKind::kQuestion && min_bp <= 1) {
    Consume();
    std::vector<Attribute> attrs = ParseAttributes();
    auto* tern = arena_.Create<Expr>();
    tern->kind = ExprKind::kTernary;
    tern->attrs = std::move(attrs);
    // §11.4.11 writes the conditional expression as its condition followed by
    // the operator, so it begins where the condition begins.
    tern->range.start = lhs->range.start;
    tern->condition = lhs;
    tern->true_expr = ParseExpr();
    Expect(TokenKind::kColon, Subclause("11.4.11"));
    // §11.3.2's Table 11-2 (printed page 272) ranks the conditional operator
    // above -> and <-> and makes it right associative. The false expression is
    // therefore read at the binding power of ||, the operator just above the
    // conditional, so an implication or an equivalence after it takes the
    // whole conditional as its left operand, and a conditional written next is
    // one more nested to the right. Reading it at the lowest power had
    // `a ? b : c -> d` take the implication into the false expression.
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
    // The clause after the operator is an expression, or a cond_pattern of
    // one, and the `?` of A.8.3 after the last clause takes the whole
    // predicate as its condition, so the clause is read short of a `?` and
    // then given its `matches` pattern. It is no pattern itself, not even after
    // a pattern-matching case item's pattern (A.6.7).
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

  // A cond_pattern's expression is any expression, an implication included
  // (A.8.3), so `matches` is read only at the lowest binding power and never
  // inside an implication's right operand.
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
    // §16.12.7: inside a sequence body an implication operator ends the
    // operand, the antecedent, rather than joining it to the consequent.
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
    // §A.8.3 inc_or_dec_expression allows an attribute_instance between the
    // prefix ++/-- operator and its variable_lvalue.
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
    // §A.8.3 expression/constant_expression allow an attribute_instance between
    // a unary_operator and its (constant_)primary.
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
    // A.2.4's dynamic_array_new writes `( expression )` after the size: one
    // expression, the array whose elements the new one starts with (§7.5.1).
    // Any other count is reported, and the list read whole so the parse goes
    // on.
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
    // A.2.4 gives class_new a list_of_arguments, the same production a
    // subroutine call takes, so the named forms A.8.2 spells are read here as
    // ParseCallExpr reads them; the dynamic_array_new branch above keeps its
    // single parenthesized expression.
    ParseListOfArguments(expr);
  }

  if (StartsShallowCopySource()) expr->lhs = ParseExpr();
  return expr;
}

// Whether `kind` ends a tagged expression or pattern whose member is written
// without a value: what follows a whole expression or pattern, the `&&&` and
// `?` of §12.6 after a pattern among them, so a `?` straight after a void
// member's name ends it.
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
      // Syntax 12-4: the member pattern of `tagged M p` ends where the pattern
      // does, so it is read at the binding power a `matches` pattern is read
      // at (TryParseSpecialInfix), short of the `&&&` filter of §12.6.1 and
      // §12.6.2 and the `?` of §12.6.3 that follow the whole pattern.
      expr->lhs = ParseExprBp(2);
    } else if (InfixBindingPower(CurrentToken().kind).first < 0) {
      // A.8.3: in an expression the member's value is a primary, so an
      // operator after the value takes the whole tagged expression as its
      // operand, and one straight after the member name, a `-` included,
      // leaves the member without a value.
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
  // §8.11 makes `this` a handle to the object the method runs in (printed
  // page 187 of IEEE 1800-2023), and a name reached through it takes the
  // postfix chain any name takes -- A.8.4's method_call and A.8.6's select run
  // on -- so `this.m[k].kill()` is read here as `m[k].kill()` is, through the
  // loop ParseIdentifierExpr uses. Reading one call and one select then
  // stopping left the `.` before kill unread, and the statement was reported as
  // missing its ';'.
  return ParseNameTail(result);
}

// Declared in parser/expr_parser_internal.h, because the literal parsing in
// expr_parser_literals.cpp builds one of these for a sized integer literal
// followed by '(expr).
Expr* MakeNodeCast(Arena& arena, Expr* type_node, Expr* value) {
  auto* cast = arena.Create<Expr>();
  cast->kind = ExprKind::kCast;
  cast->range.start = type_node->range.start;
  cast->rhs = type_node;
  cast->lhs = value;
  return cast;
}

// Builds a bare identifier node carrying the given name text and location.
// Pure node construction; declared in expr_parser_internal.h for the loop
// generate header in parser_generate.cpp, so it stands outside the unnamed
// namespace the other node builders share.
Expr* MakeIdentifierNode(Arena& arena, std::string_view text, SourceLoc loc) {
  auto* id = arena.Create<Expr>();
  id->kind = ExprKind::kIdentifier;
  id->text = text;
  id->range.start = loc;
  return id;
}

// Builds a cast whose target type is carried by a name string (cast->text) and
// whose value is carried by cast->lhs, starting at the given location. Pure
// node construction; declared in expr_parser_internal.h for the void cast
// statement in parser_stmt.cpp, so it stands outside the unnamed namespace
// the other node builders share.
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

// type_reference primary ('type(...)' or the 'type' keyword), optionally used
// as the casting_type of an assignment-pattern cast or, §6.23 listing casts
// among the uses of a type reference, of a `'(expression)` cast. A.8.2 makes
// either cast, a primary, the root a method call may follow.
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

// A.8.2 makes any primary a method call's root (method_call_root), so a
// literal, a size cast, an assignment pattern, null and $ each take the method
// tail the other primaries take: `"abc".len()`, `T'{1, 2}.sum()`.
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

  // §7.4.1 (printed page 153) allows more than one packed dimension on a
  // vector type, declaring `bit [0:3] [7:0] packedArray;` as its example, so a
  // keyword base takes every bracketed range written on it rather than the
  // first alone. Parser::ParseIdentifierPostfixChain already loops this way for
  // a name base, which is why `word_t [3:0][7:0]` parses and, until this loop,
  // `logic [3:0][7:0]` left its second range for the caller to trip over.
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
  // §23.7 states the member select written with '.' and §23.7.1 the name
  // written after a package or class scope resolution operator, so which rule a
  // missing member name breaches depends on the operator that introduced it.
  // §18.7.1: local::this names the this of the scope containing a
  // randomize() call, so `this` is a member a scope resolution may name, as
  // `super` is among the method keywords.
  auto member_tok =
      IsMethodKeyword(CurrentToken().kind) ||
              (is_scope && Check(TokenKind::kKwThis))
          ? Consume()
          : ExpectIdentifier(Subclause(is_scope ? "23.7.1" : "23.7"));
  // §8.12: a typed constructor call (§8.8) may not make a shallow copy. A.2.4
  // gives class_new the two alternatives
  // `[ class_scope ] new [ ( list_of_arguments ) ]` and `new expression`, and
  // only the second takes the copy source, so no legal parse puts a copy source
  // after a class-scoped `new`. Consuming that source leaves the caller a
  // well-formed scope resolution instead of an operand standing where a
  // terminator belongs, which is what drew the §12.3 report this replaces.
  // `is_scope` is required because `super.new` is §8.17 and a `.new` member
  // select is not a typed constructor call. What counts as a copy source is
  // Parser::StartsShallowCopySource in src/parser/expr_parser_aux.cpp, which
  // Parser::ParseNewExpr asks as well, so `C::new this` is reported here rather
  // than accepted there.
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

// An identifier or scoped name may be the casting_type of a cast: "id'{...}"
// (assignment-pattern cast) or "id'(expr)" (value cast). Returns the cast node
// when one is recognized, leaving *handled true; otherwise returns base with
// *handled false and the lexer position restored.
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

// Parse the run of postfix call/select operators (with optional intervening
// attribute lists and trailing member accesses) that follow a name primary.
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
      result = ParseSelectExpr(result);
    }
    // §23.6 Syntax 23-7 gives a hierarchical name as
    // `{ identifier constant_bit_select . } identifier`, so any number of
    // members may follow a select and not just one. Taking a single member
    // left the rest of the name unread: `a[0].b` parsed and `a[0].b.c` stopped
    // at the second period, which is why `defparam b[0].u.P = 99;` was
    // reported as a defparam missing its `=`.
    while (Check(TokenKind::kDot) || Check(TokenKind::kColonColon)) {
      result = MakeMemberAccess(result);
    }
  }
  return result;
}

// Parse the member/select tail that may follow a 'with' clause expression or
// a system call: its selects, and the methods Parser::ParseMethodTail reads
// after each '.'.
Expr* Parser::ParseWithClauseTail(Expr* result) {
  while (Check(TokenKind::kDot) || AtSelectBracket()) {
    result = Check(TokenKind::kDot) ? ParseMethodTail(result)
                                    : ParseSelectExpr(result);
  }
  return result;
}

// §A.9.3 ps_type_identifier admits a "local ::" scope prefix (footnote 48),
// used inside an inline randomize()...with constraint to bind a name in the
// calling scope rather than the randomized object (see 18.7.1); the same
// prefix also opens §A.8.4 class_qualifier. Parse it as a scope-resolution
// chain so a trailing type identifier can still form a cast
// ("local::T'(expr)"). A bare "local" without "::" is not an expression, so
// this keeps that error path intact rather than treating "local" as a name.
Expr* Parser::ParseLocalScopeExpr() {
  auto tok = Consume();  // 'local'
  if (!Check(TokenKind::kColonColon)) {
    diag_.Error(tok.loc, "'local' may only appear here as a 'local::' prefix",
                Subclause("18.7.1"));
    return MakeErrorExpr(arena_, tok.loc);
  }
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

  // §8.25.1: a parameterized class scope ("C#(5)::f()") is class_type with a
  // parameter_value_assignment, i.e. a name followed by "#(...)". The name need
  // not be a previously declared type for this to be grammatical, so recognize
  // it by the "#(" lookahead rather than by type knowledge (which fails for
  // forward-referenced parameterized classes).
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

// Whether `callee` is `super.new`, the one call A.1.9 lets write `default` in
// place of its arguments (§8.17).
bool IsSuperNewCallee(const Expr* callee) {
  return callee != nullptr && callee->kind == ExprKind::kMemberAccess &&
         callee->lhs->text == "super" && callee->rhs->text == "new";
}

}  // namespace

void Parser::ParseCallArgs(Expr* call) {
  if (Check(TokenKind::kKwDefault)) {
    auto tok = Consume();
    // A.8.2's list_of_arguments holds no `default`, which stands for a
    // constructor's arguments in its super.new call alone.
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
  // A.8.2 writes an argument list after the name of a subroutine or a method
  // alone, so none follows a call, `f(1)(2)`, or a select, `a[0](1)`.
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

// 18.7: capture a randomize() with { constraint_block } body, positioned just
// past the opening '{'. The block's inline constraints follow the same rules
// and take the same forms as an in-class constraint block, so the body is
// scanned by the shared constraint-body scanner into a throwaway constraint
// member; the simulator later applies its captured relations alongside the
// object's own constraints. The scan consumes through the matching '}'.
ClassMember* Parser::CaptureInlineConstraintBlock() {
  auto* block = arena_.Create<ClassMember>();
  block->kind = ClassMemberKind::kConstraint;
  ScanConstraintBodyRelations(block);
  return block;
}

// §16.9.2: in a sequence body a `[` after an operand may open a repetition,
// `[*`, `[->`, `[=` or `[+]`, rather than a select; while the linear capture
// reads such a body, an expression stops before one, leaving it to the
// capture, and everywhere else a `[` is the select it has always been.
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
  // §11.5.1 writes a select as its base followed by the bracketed address, so
  // the select starts where its base does. Without this the node carries no
  // position at all, and a report standing at a select renders as
  // "<unknown location>".
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
