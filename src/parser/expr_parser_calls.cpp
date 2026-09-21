#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/parser.h"

namespace delta {

// Builds the scoped identifier expression produced by a "$unit::id" or
// "$root.id" system-keyword prefix (see 23.7.1 scope resolution /
// hierarchical names). The named scope keyword is recorded in scope_prefix.
Expr* Parser::MakeSysScopePrefix(const Token& sys_tok) {
  auto id = ExpectIdentifier(Subclause("23.7.1"));
  auto* expr = arena_.Create<Expr>();
  expr->kind = ExprKind::kIdentifier;
  expr->text = id.text;
  expr->scope_prefix = sys_tok.text;
  expr->range.start = sys_tok.loc;
  return expr;
}

// Parses the trailing select/event syntax of a "$root.id..." hierarchical
// name: any further member accesses followed by an optional bit/part select.
Expr* Parser::ParseSysRootTail(Expr* expr) {
  while (Check(TokenKind::kDot) || Check(TokenKind::kColonColon)) {
    expr = MakeMemberAccess(expr);
  }
  if (AtSelectBracket()) expr = ParseSelectExpr(expr);
  return expr;
}

// Consumes one "@event" clocking-event argument. Annex C.2.2: the clocking
// event argument to $sampled was removed, so $sampled no longer accepts one
// (other sampled value functions still take a clocking event, see 16.9.3).
void Parser::ParseSysClockingEventArg(Expr* call) {
  if (call->callee == "$sampled") {
    diag_.Error(CurrentLoc(),
                "$sampled does not accept a clocking event argument",
                Subclause("16.9.3"));
  }
  Consume();
  if (Match(TokenKind::kLParen)) {
    ParseEventList();
    Expect(TokenKind::kRParen, Subclause("16.9.3"));
  } else {
    Consume();
  }
}

// Parses the comma-separated argument list, appending each argument (or
// nullptr for an empty slot) to call->args; an "@event" terminates the list.
void Parser::ParseSysCallArgs(Expr* call) {
  if (Check(TokenKind::kComma)) {
    call->args.push_back(nullptr);
  } else {
    call->args.push_back(ParseExpr());
  }
  while (Match(TokenKind::kComma)) {
    if (Check(TokenKind::kAt)) {
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

Expr* Parser::ParseSystemCall() {
  auto tok = Consume();

  if (IsTimingCheckName(tok.text)) {
    diag_.Error(tok.loc, "timing check cannot appear in procedural code",
                Subclause("31.2"));
  }

  // §3.12.1 (printed page 56) makes `$unit::` the explicit reference to an
  // identifier of the compilation-unit scope, and A.8.4's primary (printed
  // 1211) gives that identifier the select and method-call chain any
  // hierarchical identifier takes, so `$unit::q.size()`, `$unit::s.len()`
  // and `$unit::arr[0]` read through the same tail a `$root.` name reads
  // and the same postfix loop a bare name takes (ParseIdentifierPostfixChain,
  // expr_parser.cpp). Returned as the prefixed identifier alone, each was
  // reported as a statement missing its ';' at the `.` or `[`. The head
  // identifier keeps the prefix in Expr::scope_prefix, which the simulator
  // resolves the unit's storage by (IdentifierLookupKey in
  // src/simulator/eval_function_args_scoped.cpp).
  if (tok.text == "$unit" && Check(TokenKind::kColonColon)) {
    Consume();
    return ParseIdentifierPostfixChain(
        ParseSysRootTail(MakeSysScopePrefix(tok)));
  }
  if (tok.text == "$root" && Check(TokenKind::kDot)) {
    Consume();
    return ParseSysRootTail(MakeSysScopePrefix(tok));
  }

  auto* call = arena_.Create<Expr>();
  call->kind = ExprKind::kSystemCall;
  call->callee = tok.text;
  call->range.start = tok.loc;
  if (!Match(TokenKind::kLParen)) {
    if (AtSelectBracket()) return ParseSelectExpr(call);
    return call;
  }

  if (!Check(TokenKind::kRParen)) {
    ParseSysCallArgs(call);
  }
  Expect(TokenKind::kRParen, Subclause("13.5"));
  if (AtSelectBracket()) return ParseSelectExpr(call);
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
    return cat;
  }

  if (Check(TokenKind::kLtLt) || Check(TokenKind::kGtGt)) {
    auto dir = CurrentToken().kind;
    auto* sc = ParseStreamingConcat(dir);
    Expect(TokenKind::kRBrace, Subclause("11.4.14"));
    return sc;
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

    if (AtSelectBracket()) return ParseSelectExpr(rep);
    return rep;
  }

  auto* cat = arena_.Create<Expr>();
  cat->kind = ExprKind::kConcatenation;
  cat->range.start = loc;
  cat->elements.push_back(first);
  while (Match(TokenKind::kComma)) {
    cat->elements.push_back(ParseExpr());
  }
  Expect(TokenKind::kRBrace, Subclause("11.4.12"));

  if (AtSelectBracket()) return ParseSelectExpr(cat);
  return cat;
}

// A.8.4 lists a cast among the primaries and A.8.6 makes a primary the root
// of a method call, `method_call_root . method_identifier`, so a member
// select and a call may follow a cast: `Cols'(2).name()` is name() on the
// value cast to Cols (§6.19.5.6), `string'(v).len()` len() on the string
// (§6.16.1), and `Cols'(1).next` the call with no argument list (§6.19.5.7).
// Read as ending at the cast's ')', the '.' was reported as an unexpected
// token. A select follows no cast: A.8.4 has a bit-select or part-select
// apply to a hierarchical identifier and not to a primary.
Expr* Parser::ParseCastMethodTail(Expr* cast) {
  while (Check(TokenKind::kDot)) {
    cast = MakeMemberAccess(cast);
    if (Check(TokenKind::kLParen)) cast = ParseCallExpr(cast);
  }
  return cast;
}

Expr* Parser::ParseCastExpr() {
  auto type_tok = Consume();
  // A.8.4's casting_type is `simple_type | constant_primary | signing |
  // string | const`, and `void` is none of them: A.6.9 writes `void ' (
  // function_subroutine_call ) ;` as a subroutine_call_statement and nowhere
  // else, §13.4.1 having it discard a function's return value "as a
  // statement". Parser::ParseVoidCastCallStmt reads that statement, so a
  // `void'` reaching the expression parser stands where an expression does.
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
  return ParseCastMethodTail(cast);
}

// A.2.10: the `with [ ... ]` array range of a §7.12.1 array manipulation call
// -- a single index, a ranged pair, or an indexed part-select.
Expr* Parser::ParseWithClauseRange() {
  auto* range = arena_.Create<Expr>();
  range->kind = ExprKind::kSelect;
  range->index = ParseExpr();
  // Parser::ParseWithClause consumed the `[`, so what remains of the §7.12.1
  // array range is the bounds, and the range begins where the first one does.
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
  return range;
}

// A.8.2: a randomize_call's with-clause allows an identifier_list inside the
// parentheses, while an array_manipulation_call's carries a single expression.
// Either is tolerated: the first entry becomes the with-expression, and every
// entry that is a bare identifier is collected as a name.
std::vector<std::string_view> Parser::ParseWithClauseIdentifiers(Expr* expr) {
  std::vector<std::string_view> ids;
  if (Check(TokenKind::kRParen)) return ids;
  expr->with_expr = ParseExpr();
  if (expr->with_expr != nullptr &&
      expr->with_expr->kind == ExprKind::kIdentifier)
    ids.push_back(expr->with_expr->text);
  while (Match(TokenKind::kComma)) {
    Expr* next_id = ParseExpr();
    if (next_id != nullptr && next_id->kind == ExprKind::kIdentifier)
      ids.push_back(next_id->text);
  }
  return ids;
}

Expr* Parser::ParseWithClause(Expr* expr) {
  if (!Match(TokenKind::kKwWith)) return expr;

  if (Check(TokenKind::kLBrace)) {
    Consume();
    expr->inline_constraint = CaptureInlineConstraintBlock();
    return expr;
  }

  if (Check(TokenKind::kLBracket)) {
    Consume();
    expr->with_expr = ParseWithClauseRange();
    Expect(TokenKind::kRBracket, Subclause("7.12.1"));
    return expr;
  }
  Expect(TokenKind::kLParen, Subclause("7.12"));
  expr->with_has_parens = true;
  std::vector<std::string_view> ids = ParseWithClauseIdentifiers(expr);
  Expect(TokenKind::kRParen, Subclause("7.12"));

  if (Check(TokenKind::kLBrace)) {
    Consume();
    expr->inline_constraint = CaptureInlineConstraintBlock();
    // 18.7: the parenthesized names are the identifier_list of a restricted
    // constraint block; keep them so the simulator limits which names resolve
    // as the object's random variables. Recorded only when a constraint block
    // actually follows, leaving the shared array-method `with (expr)` form (no
    // trailing block) untouched.
    expr->with_restrict_ids = std::move(ids);
  }
  return expr;
}

}  // namespace delta
