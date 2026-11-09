#include <cstdint>
#include <format>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "lexer/lexer.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "parser/display_format_check.h"
#include "parser/expr_parser_internal.h"
#include "parser/parser.h"

namespace delta {

namespace {

Expr* UnitScopedTypeName(Arena& arena, const Token& unit_tok,
                         const Expr* name) {
  auto* acc = arena.Create<Expr>();
  acc->kind = ExprKind::kMemberAccess;
  acc->lhs = MakeIdentifierNode(arena, unit_tok.text, unit_tok.loc);
  acc->rhs = MakeIdentifierNode(arena, name->text, name->range.start);
  acc->is_scope_resolution = true;
  acc->range.start = unit_tok.loc;
  return acc;
}

}  // namespace

Expr* Parser::MakeSysScopePrefix(const Token& sys_tok) {
  auto id = ExpectIdentifier(Subclause("23.7.1"));
  auto* expr = arena_.Create<Expr>();
  expr->kind = ExprKind::kIdentifier;
  expr->text = id.text;
  expr->scope_prefix = sys_tok.text;
  expr->range.start = sys_tok.loc;
  return expr;
}

Expr* Parser::ParseSysRootTail(Expr* expr) {
  while (Check(TokenKind::kDot) || Check(TokenKind::kColonColon)) {
    expr = MakeMemberAccess(expr);
  }
  if (AtSelectBracket()) expr = ParseSelectExpr(expr);
  return expr;
}

Expr* Parser::ParseNameTail(Expr* result) {
  result = ParseIdentifierPostfixChain(result);
  if (Check(TokenKind::kPlusPlus) || Check(TokenKind::kMinusMinus)) {
    auto op_tok = Consume();
    CheckIncDecOperand(result, diag_);
    return MakePostfixUnary(arena_, op_tok.kind, result);
  }
  result = ParseWithClause(result);
  if (!result->with_expr) return result;
  return ParseWithClauseTail(result);
}

void Parser::ParseSysClockingEventArg(Expr* call) {
  if (call->callee == "$sampled") {
    diag_.Error(CurrentLoc(),
                "$sampled does not accept a clocking event argument",
                Subclause("16.9.3"));
  }
  Consume();
  auto* clock = arena_.Create<std::vector<EventExpr>>();
  if (Match(TokenKind::kLParen)) {
    *clock = ParseEventList();
    Expect(TokenKind::kRParen, Subclause("16.9.3"));
  } else {
    clock->push_back(ParseNamedClockingEvent());
  }
  call->sampled_clock = clock;
}

void Parser::ParseSysCallArgs(Expr* call) {
  if (Check(TokenKind::kComma)) {
    call->args.push_back(nullptr);
  } else {
    call->args.push_back(ParseTypeOr(&Parser::ParseExpr));
  }
  while (Match(TokenKind::kComma)) {
    if (Check(TokenKind::kAt)) {
      if (call->args.front() == nullptr) {
        diag_.Error(CurrentLoc(),
                    "a clocking event follows a system call's arguments only "
                    "after a first expression",
                    Subclause("A.8.2"));
      }
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

Expr* Parser::ParseUnitScopedName(const Token& unit_tok) {
  Expr* name = MakeSysScopePrefix(unit_tok);
  bool cast_handled = false;
  Expr* cast = TryParseIdentifierCast(
      UnitScopedTypeName(arena_, unit_tok, name), &cast_handled);
  if (cast_handled) return cast;
  Expr* chain = ParseSysRootTail(ParseScopeSpecialization(name));
  cast = TryParseIdentifierCast(chain, &cast_handled);
  if (cast_handled) return cast;
  return ParseNameTail(chain);
}

Expr* Parser::ParseSystemCall() {
  auto tok = Consume();

  if (IsTimingCheckName(tok.text)) {
    diag_.Error(tok.loc, "timing check cannot appear in procedural code",
                Subclause("31.2"));
  }

  if (tok.text == "$unit" && Match(TokenKind::kColonColon)) {
    return ParseUnitScopedName(tok);
  }
  if (tok.text == "$unit" && Check(TokenKind::kDot)) {
    Consume();
    Expr* name = MakeSysScopePrefix(tok);
    diag_.Error(
        tok.loc,
        std::format("'$unit.{}' names nothing: $unit selects a "
                    "declaration of the compilation-unit scope only "
                    "through '::', and no hierarchical name reaches one",
                    name->text),
        Subclause("3.12.1"));
    return ParseNameTail(ParseSysRootTail(name));
  }
  if (tok.text == "$root" && Check(TokenKind::kDot)) {
    Consume();
    return ParseNameTail(ParseSysRootTail(MakeSysScopePrefix(tok)));
  }

  auto* call = arena_.Create<Expr>();
  call->kind = ExprKind::kSystemCall;
  call->callee = tok.text;
  call->range.start = tok.loc;
  if (!Match(TokenKind::kLParen)) {
    if (AtSelectBracket()) return ParseSelectExpr(call);
    return call;
  }
  call->has_arg_list = true;

  if (!Check(TokenKind::kRParen)) {
    ParseSysCallArgs(call);
  }
  Expect(TokenKind::kRParen, Subclause("13.5"));
  CheckDisplayFormatLiterals(call, diag_);
  if (Check(TokenKind::kDot) || AtSelectBracket())
    return ParseWithClauseTail(call);
  return call;
}

Expr* Parser::ParseConcatenation() {
  auto loc = CurrentLoc();
  Expect(TokenKind::kLBrace, Subclause("11.4.12"));

  if (Check(TokenKind::kRBrace)) {
    Consume();
    auto* cat = arena_.Create<Expr>();
    cat->kind = ExprKind::kConcatenation;
    cat->range.start = loc;
    return ParseParenMethodTail(cat);
  }

  if (Check(TokenKind::kLtLt) || Check(TokenKind::kGtGt)) {
    auto dir = CurrentToken().kind;
    auto* sc = ParseStreamingConcat(dir);
    Expect(TokenKind::kRBrace, Subclause("11.4.14"));
    return ParseParenMethodTail(sc);
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
    Expect(TokenKind::kRBrace, Subclause("11.4.12.1"));
    Expect(TokenKind::kRBrace, Subclause("11.4.12.1"));
    ReportEmptyConcatItems(rep, diag_);

    return ParseParenMethodTail(AtSelectBracket() ? ParseSelectExpr(rep) : rep);
  }

  auto* cat = arena_.Create<Expr>();
  cat->kind = ExprKind::kConcatenation;
  cat->range.start = loc;
  cat->elements.push_back(first);
  while (Match(TokenKind::kComma)) {
    cat->elements.push_back(ParseExpr());
  }
  Expect(TokenKind::kRBrace, Subclause("11.4.12"));
  ReportEmptyConcatItems(cat, diag_);

  return ParseParenMethodTail(AtSelectBracket() ? ParseSelectExpr(cat) : cat);
}

Expr* Parser::ParseMethodTail(Expr* root) {
  while (Check(TokenKind::kDot)) {
    root = MakeMemberAccess(root);
    ParseAttributes();
    if (Check(TokenKind::kLParen)) root = ParseCallExpr(root);
    root = ParseWithClause(root);
  }
  return root;
}

Expr* Parser::ParseCastExpr() {
  auto type_tok = Consume();
  if (type_tok.kind == TokenKind::kKwVoid) {
    diag_.Error(type_tok.loc,
                "a void cast is a statement, void'(function_subroutine_call); "
                "and no expression, 'void' being no casting_type",
                Subclause("A.6.9"));
  }
  Expect(TokenKind::kApostrophe, Subclause("6.24.1"));
  Expect(TokenKind::kLParen, Subclause("6.24.1"));
  auto* cast = arena_.Create<Expr>();
  cast->kind = ExprKind::kCast;
  cast->text = type_tok.text;
  cast->range.start = type_tok.loc;
  cast->lhs = ParseExpr();
  Expect(TokenKind::kRParen, Subclause("6.24.1"));
  return ParseMethodTail(cast);
}

bool WithOpensRange(Lexer& lexer) {
  if (lexer.Peek().kind != TokenKind::kKwWith) return false;
  Lexer::SavedPos saved = lexer.SavePos();
  lexer.Next();
  bool opens_range = lexer.Peek().kind == TokenKind::kLBracket;
  lexer.RestorePos(saved);
  return opens_range;
}

void ReportPredicateOperator(const Expr* e, DiagEngine& diag) {
  if (e->kind == ExprKind::kBinary &&
      (e->op == TokenKind::kKwMatches || e->op == TokenKind::kAmpAmpAmp)) {
    diag.Error(e->range.start,
               "'matches' and '&&&' stand only in the predicate of an if "
               "statement or a conditional operator",
               Subclause("A.6.6"));
  }
}

void ReportEmptyConcatItems(const Expr* concat, DiagEngine& diag) {
  for (const Expr* item : concat->elements) {
    if (item->kind == ExprKind::kConcatenation && item->elements.empty()) {
      diag.Error(item->range.start,
                 "an empty concatenation, {}, is the empty unpacked array "
                 "concatenation and no item of another concatenation",
                 Subclause("A.8.1"));
    }
  }
}

Expr* Parser::ParseWithClauseRange(bool in_stream_expression) {
  Token with_tok = Consume();
  if (!in_stream_expression) {
    diag_.Error(with_tok.loc,
                "a with range follows only the operand of a stream expression "
                "in a streaming concatenation",
                Subclause("A.8.1"));
  }
  Consume();
  auto* range = arena_.Create<Expr>();
  range->kind = ExprKind::kSelect;
  range->index = ParseExpr();
  range->range.start = range->index->range.start;
  if (Match(TokenKind::kPlusColon)) {
    range->is_part_select_plus = true;
    range->index_end = ParseExpr();
  } else if (Match(TokenKind::kMinusColon)) {
    range->is_part_select_minus = true;
    range->index_end = ParseExpr();
  } else if (Match(TokenKind::kColon)) {
    range->index_end = ParseExpr();
  }
  Expect(TokenKind::kRBracket, Subclause("11.4.14.4"));
  return range;
}

void Parser::ParseRandomizeWith(Expr* call) {
  if (Match(TokenKind::kLParen)) {
    call->with_has_parens = true;
    bool more = !Check(TokenKind::kRParen);
    while (more) {
      const Expr* entry = ParseExpr();
      if (entry->kind == ExprKind::kIdentifier) {
        call->with_restrict_ids.push_back(entry->text);
      } else {
        diag_.Error(entry->range.start,
                    "a randomize call's with clause lists identifiers alone "
                    "in its parentheses",
                    Subclause("A.8.2"));
      }
      more = Match(TokenKind::kComma);
    }
    Expect(TokenKind::kRParen, Subclause("18.7"));
  }
  if (!Check(TokenKind::kLBrace)) {
    diag_.Error(CurrentLoc(),
                "a randomize call's with clause ends in a constraint block",
                Subclause("A.8.2"));
    return;
  }
  Consume();
  call->inline_constraint = CaptureInlineConstraintBlock();
}

namespace {

enum class WithHost : std::uint8_t { kNone, kArrayMethod, kRandomize };

WithHost WithHostOf(const Expr* e) {
  const Expr* name = e->kind == ExprKind::kCall ? e->lhs : e;
  if (name->kind == ExprKind::kIdentifier) {
    return name->text == "randomize" ? WithHost::kRandomize : WithHost::kNone;
  }
  if (name->kind != ExprKind::kMemberAccess) return WithHost::kNone;
  const bool kRandomize = name->rhs->text == "randomize";
  if (!name->is_scope_resolution) {
    return kRandomize ? WithHost::kRandomize : WithHost::kArrayMethod;
  }
  return kRandomize && name->lhs->text == "std" ? WithHost::kRandomize
                                                : WithHost::kNone;
}

constexpr const char* kOneWithExpression =
    "an array method's with clause holds one expression in its parentheses";

Expr* RandomizeCallOf(Expr* name, Arena& arena) {
  auto* call = arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = name->text;
  call->lhs = name;
  call->range.start = name->range.start;
  return call;
}

bool IsStdRandomizeName(const Expr* e) {
  return e->kind == ExprKind::kMemberAccess && e->is_scope_resolution &&
         WithHostOf(e) == WithHost::kRandomize;
}

}  // namespace

Expr* Parser::ParseWithClause(Expr* expr) {
  if (!Check(TokenKind::kKwWith) || WithOpensRange(lexer_)) {
    return IsStdRandomizeName(expr) ? RandomizeCallOf(expr, arena_) : expr;
  }
  const WithHost kHost = WithHostOf(expr);
  const Token kWith = Consume();
  if (kHost == WithHost::kRandomize) {
    Expr* call =
        expr->kind == ExprKind::kCall ? expr : RandomizeCallOf(expr, arena_);
    ParseRandomizeWith(call);
    return call;
  }
  if (kHost == WithHost::kNone) {
    diag_.Error(
        kWith.loc,
        "a with clause follows only an array method call or a randomize call",
        Subclause("A.8.2"));
  }
  if (!Check(TokenKind::kLBrace)) {
    Expect(TokenKind::kLParen, Subclause("7.12"));
    expr->with_has_parens = true;
    if (Check(TokenKind::kRParen)) {
      diag_.Error(CurrentLoc(), kOneWithExpression, Subclause("A.8.2"));
    } else {
      expr->with_expr = ParseExpr();
    }
    while (Check(TokenKind::kComma)) {
      diag_.Error(CurrentLoc(), kOneWithExpression, Subclause("A.8.2"));
      Consume();
      ParseExpr();
    }
    Expect(TokenKind::kRParen, Subclause("7.12"));
  }
  if (Check(TokenKind::kLBrace)) {
    diag_.Error(CurrentLoc(),
                "an array method's with clause takes no constraint block",
                Subclause("A.8.2"));
    Consume();
    CaptureInlineConstraintBlock();
  }
  return expr;
}

namespace {

bool IsSelectedName(const Expr* arg) {
  return arg->kind == ExprKind::kMemberAccess || arg->kind == ExprKind::kSelect;
}

void ReportRandomizeArg(const Expr* call, const Expr* arg, bool bare,
                        bool std_form, DiagEngine& diag) {
  if (arg == nullptr) {
    diag.Error(call->range.start,
               "a randomize call's argument list leaves no position empty",
               Subclause("A.8.2"));
    return;
  }
  if (arg->kind == ExprKind::kIdentifier) {
    if (arg->text == "null" && call->args.size() > 1) {
      diag.Error(arg->range.start,
                 "'null' stands alone in a randomize call's argument list",
                 Subclause("A.8.2"));
    }
    return;
  }
  if (std_form) {
    diag.Error(arg->range.start,
               "argument to std::randomize shall be a variable identifier",
               Subclause("G.5"));
    return;
  }
  if (bare && IsSelectedName(arg)) return;
  diag.Error(arg->range.start,
             "randomize() arguments shall be object property names, not "
             "expressions",
             Subclause("18.11"));
}

}  // namespace

void Parser::CheckRandomizeArgList(const Expr* call) {
  const Expr* callee = call->lhs;
  const bool kBare = call->callee == "randomize";
  if (!kBare && (callee->kind != ExprKind::kMemberAccess ||
                 callee->rhs->text != "randomize")) {
    return;
  }
  const bool kStd =
      !kBare && callee->is_scope_resolution && callee->lhs->text == "std";
  if (!call->arg_names.empty()) {
    diag_.Error(call->range.start,
                "a randomize call passes no argument by name",
                Subclause("A.8.2"));
  }
  for (const Expr* arg : call->args) {
    ReportRandomizeArg(call, arg, kBare, kStd, diag_);
  }
}

}  // namespace delta
