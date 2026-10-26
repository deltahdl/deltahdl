#include <cstdint>
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

// A.9.3 makes `$unit ::` a package_scope, so the type a cast names through it
// is written as the scope resolution a package's type is, `$unit :: T` as
// `P :: T`: the cast then reads its type under the "$unit::T" key the
// elaborator records the unit's typedefs by (RegisterUnitScopedType).
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

// A.8.4 gives a name primary, whether a bare identifier, `this` or `super`, or
// `$root.` (§23.6) heads it, one tail: the calls and selects of
// ParseIdentifierPostfixChain, then a postfix increment or decrement (§11.4.2),
// or a `with` clause (§18.7) and the members and selects that follow it.
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
  // §16.9.3: the event is the function's own clock, kept on the call, written
  // in parentheses or, §9.4 Syntax 9-4, as a bare name.
  auto* clock = arena_.Create<std::vector<EventExpr>>();
  if (Match(TokenKind::kLParen)) {
    *clock = ParseEventList();
    Expect(TokenKind::kRParen, Subclause("16.9.3"));
  } else {
    clock->push_back(ParseNamedClockingEvent());
  }
  call->sampled_clock = clock;
}

// Parses the comma-separated argument list, appending each argument (or
// nullptr for an empty slot) to call->args; an "@event" terminates the list.
// A.8.2 lets the first argument be a data_type, which $bits, $typename and the
// array queries take (§20.6, §20.7), and writes the clocking event only after
// a first expression.
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
  // and the same name tail a bare name takes (ParseNameTail), whose with
  // clause A.8.2 gives an array method on the name, `$unit::q.find with
  // (item > 0)`. Returned as the prefixed identifier alone, each was
  // reported as a statement missing its ';' at the `.` or `[`. The head
  // identifier keeps the prefix in Expr::scope_prefix, which the simulator
  // resolves the unit's storage by (IdentifierLookupKey in
  // src/simulator/eval_function_args_scoped.cpp). A.8.4 makes the name the
  // casting type of a cast where `'(` or `'{` follows it, as
  // TryParseIdentifierCast reads one after `P::T`; left to the tail,
  // `$unit::T'(x)` stopped at the `'`.
  if (tok.text == "$unit" && Check(TokenKind::kColonColon)) {
    Consume();
    Expr* name = MakeSysScopePrefix(tok);
    bool cast_handled = false;
    Expr* cast = TryParseIdentifierCast(UnitScopedTypeName(arena_, tok, name),
                                        &cast_handled);
    if (cast_handled) return cast;
    return ParseNameTail(ParseSysRootTail(name));
  }
  // §23.6 lets `$root` head a hierarchical name, and the name takes the tail
  // any name primary takes: `$root.top.arr[1][0]` and `$root.m.u.d.f()` were
  // read up to their first select and stopped there, the second `[` and the
  // call's `(` reported as unexpected.
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
  // A.8.4 (printed page 1211): a system function call is a primary, and a
  // method call's root is any primary (method_call_root), so the call may be
  // followed by a method or a select as any other primary may --
  // `$sformatf("%s", s).len()`, `$sformatf(...).substr(0, 1).toupper()`.
  if (Check(TokenKind::kDot) || AtSelectBracket())
    return ParseWithClauseTail(call);
  return call;
}

Expr* Parser::ParseConcatenation() {
  auto loc = CurrentLoc();
  Expect(TokenKind::kLBrace, Subclause("11.4.12"));

  // A.8.2 makes any primary a method call's root, and A.8.4 counts the empty
  // unpacked array concatenation and a streaming concatenation among them.
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
  // A.8.1's footnote 40: `{}` is the empty unpacked array concatenation of
  // §10.10 alone and stands in no other concatenation as an item.
  ReportEmptyConcatItems(cat, diag_);

  // A.8.2 makes a method call's root a primary, and A.8.4 lists a
  // concatenation and a multiple concatenation, each with an optional select,
  // among the primaries, so a method call or a member select may follow either:
  // `{s, " x"}.len()` calls len() on the string the concatenation yields
  // (§11.4.12.2).
  return ParseParenMethodTail(AtSelectBracket() ? ParseSelectExpr(cat) : cat);
}

// A.8.2 makes any primary the root of a method call, `method_call_root .
// method_call_body`, so a member select and a call may follow a cast, a
// literal or an assignment pattern: `Cols'(2).name()` is name() on the value
// cast to Cols (§6.19.5.6), `string'(v).len()` len() on the string
// (§6.16.1), and `Cols'(1).next` the call with no argument list (§6.19.5.7).
// Read as ending at the cast's ')', the '.' was reported as an unexpected
// token. Each method_call_body is read whole: the method's name, the
// attribute instances written after it, its argument list where one is
// written, and an array method's or a randomize call's with clause. A select
// follows no cast: A.8.4 has a bit-select or part-select apply to a
// hierarchical identifier and not to a primary.
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
  // A.8.4's casting_type is `simple_type | constant_primary | signing |
  // string | const`, and `void` is none of them: A.6.9 writes `void ' (
  // function_subroutine_call ) ;` as a subroutine_call_statement and nowhere
  // else, §13.4.1 having it discard a function's return value when the call is
  // a statement. Parser::ParseVoidCastCallStmt reads that statement, so a
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

// A.8.1's `with [ array_range_expression ]`, read whole from the `with`: a
// single index, a ranged pair, or an indexed part-select of what the operand
// before it names (§11.4.14.4). A.8.1 writes it after the operand of a
// stream_expression alone, so where `in_stream_expression` is false it is
// reported, and read past all the same.
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
  // What follows the `[` is the bounds, and the range begins where the first
  // one does.
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

// A.8.2's randomize_call with clause after its `with`: an optional
// parenthesized identifier_list, the names a restricted inline constraint
// block resolves in the object (§18.7), which the simulator reads from
// Expr::with_restrict_ids, and then the constraint block, which is required.
// An entry that is no identifier is reported and read past.
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

// Which of A.8.2's with clauses the call before a `with` takes.
enum class WithHost : std::uint8_t { kNone, kArrayMethod, kRandomize };

// A randomize_call's for randomize written bare, under std:: or after a `.`;
// an array_manipulation_call's for any other method named after a `.`; none
// for anything else -- a name alone, a subroutine call, a select, or a name
// under a scope other than std's.
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

// A.8.2 (printed page 1209): a randomize_call's argument list is optional,
// and one written without it is the call randomize() is, built as
// Parser::ParseCallExpr builds that call, with no argument.
Expr* RandomizeCallOf(Expr* name, Arena& arena) {
  auto* call = arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = name->text;
  call->lhs = name;
  call->range.start = name->range.start;
  return call;
}

// Whether `e` is the name std::randomize, which names the scope randomize
// function and nothing else, written with no argument list.
bool IsStdRandomizeName(const Expr* e) {
  return e->kind == ExprKind::kMemberAccess && e->is_scope_resolution &&
         WithHostOf(e) == WithHost::kRandomize;
}

}  // namespace

// A.8.2's with clause: after a randomize call, the form
// Parser::ParseRandomizeWith reads; after an array method, one expression in
// parentheses and no constraint block. A with clause after anything else is
// reported and read as an array method's. A `with` that opens a bracketed
// range is left standing: A.8.1 writes that range after the whole operand of
// a stream_expression, where Parser::ParseStreamingConcat reads it.
Expr* Parser::ParseWithClause(Expr* expr) {
  if (!Check(TokenKind::kKwWith) || WithOpensRange(lexer_)) {
    return IsStdRandomizeName(expr) ? RandomizeCallOf(expr, arena_) : expr;
  }
  const WithHost kHost = WithHostOf(expr);
  const Token kWith = Consume();
  if (kHost == WithHost::kRandomize) {
    // A randomize name a with clause follows is the randomize_call written
    // without its argument list; `randomize` being no reserved word, a name
    // with neither may be a member or a variable, and stays one.
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

// §18.11 with A.8.2: an argument of a randomize() written bare that names a
// variable through another, a member access or a select, which the
// elaborator's scope randomize check reports under A.8.2.
bool IsSelectedName(const Expr* arg) {
  return arg->kind == ExprKind::kMemberAccess || arg->kind == ExprKind::kSelect;
}

// One position of a randomize call's argument list (see
// Parser::CheckRandomizeArgList). `bare` is a randomize() written alone and
// `std_form` one written std::randomize.
void ReportRandomizeArg(const Expr* call, const Expr* arg, bool bare,
                        bool std_form, DiagEngine& diag) {
  if (arg == nullptr) {
    diag.Error(call->range.start,
               "a randomize call's argument list leaves no position empty",
               Subclause("A.8.2"));
    return;
  }
  // §18.11.1: null names no random variable, standing alone; it is lexed as
  // an identifier.
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
  // A.8.2's randomize_call takes `( [ variable_identifier_list | null ] )`:
  // names separated by commas, or null alone, and §18.11 limits the class
  // method's arguments to the names of the object's properties. The call is
  // recognized as a bare randomize(...) or as a call whose member name is
  // randomize, and its list, read as any call's, is held to that form: no
  // named argument, no empty position, no null beside a name, and no argument
  // that is not a name -- under G.5 for std::randomize, which gives it the
  // same variable_identifier_list, and under §18.11 otherwise. A member access
  // or a select passed to a bare randomize() is left to the elaborator.
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
