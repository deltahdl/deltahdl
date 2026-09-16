#include "parser/parser.h"
#include "parser/parser_property_spec_internal.h"

namespace delta {

static void ExpectDeferredHashZero(DiagEngine& diag, const Token& tok) {
  if (tok.text != "0") {
    diag.Error(tok.loc,
               "deferred immediate assertion requires #0, got #" +
                   std::string(tok.text),
               Subclause("16.4"));
  }
}

// CPD-dedup: the assertion forms below are written out of the same three
// pieces of syntax — the deferral, the asserted expression and the action
// block — so each piece is read in one place here.

struct ParserAssertHelpers {
  // A.6.10's deferred_immediate_assertion_item, the alternative of A.1.4's
  // assertion_item that A.1.7's non_port_program_item leaves out, admitting a
  // concurrent_assertion_item alone: §16.4.3 has a deferred assertion outside
  // procedural code "treated as if it were contained in an always_comb
  // procedure", and §24.3 has a program that "shall not contain always
  // procedures". One in a program body is reported and still read, from the
  // assert and assume path and from the cover path alike.
  static void RejectDeferredInProgram(Parser& p, SourceLoc loc) {
    p.RejectInProgramBody(loc,
                          "a deferred immediate assertion is not an item of a "
                          "program; outside procedural code it stands for an "
                          "always_comb procedure, which a program does not "
                          "contain");
  }

  // §16.4: an immediate assertion is deferred when it is written with #0 or
  // with final. Records which of the two the source used, and rejects any
  // delay other than #0.
  static void ParseDeferral(Parser& p, Stmt* stmt) {
    if (p.Match(TokenKind::kHash)) {
      auto tok = p.Expect(TokenKind::kIntLiteral, Subclause("16.4"));
      ExpectDeferredHashZero(p.diag_, tok);
      stmt->is_deferred = true;
    } else if (p.Match(TokenKind::kKwFinal)) {
      stmt->is_deferred = true;
      stmt->is_final_deferred = true;
    }
  }

  // The parenthesized expression the assertion tests.
  static void ParseAssertedExpr(Parser& p, Stmt* stmt) {
    p.Expect(TokenKind::kLParen, Subclause("16.3"));
    stmt->assert_expr = p.ParseExpr();
    p.Expect(TokenKind::kRParen, Subclause("16.3"));
  }

  // §16.3 action_block: a pass statement, an else with a fail statement, or
  // neither, in which case a semicolon closes the assertion.
  static void ParseActionBlock(Parser& p, Stmt* stmt) {
    if (!p.Check(TokenKind::kSemicolon) && !p.Check(TokenKind::kKwElse)) {
      stmt->assert_pass_stmt = p.ParseStmt();
    }
    if (p.Match(TokenKind::kKwElse)) {
      stmt->assert_fail_stmt = p.ParseStmt();
    }
    if (!stmt->assert_pass_stmt && !stmt->assert_fail_stmt) {
      p.Expect(TokenKind::kSemicolon, Subclause("16.3"));
    }
  }

  // §16.3 Syntax 16-1 ends every `cover` form in `statement_or_null` where the
  // `assert` and `assume` forms end in `action_block`, so a `cover` takes a
  // pass statement and has no fail statement. Reports an `else` written after
  // one, and reads the statement behind it so the enclosing body never sees the
  // arm and reports it a second time as a token it did not expect. `semicolon`
  // is the subclause the closing `;` is expected under, which differs between
  // the two forms that read a cover tail.
  static void ParseCoverTail(Parser& p, Stmt* stmt, Subclause semicolon) {
    if (p.Check(TokenKind::kSemicolon)) {
      p.Expect(TokenKind::kSemicolon, semicolon);
    } else if (!p.Check(TokenKind::kKwElse)) {
      stmt->assert_pass_stmt = p.ParseStmt();
    }
    if (!p.Check(TokenKind::kKwElse)) return;
    p.diag_.Error(p.CurrentLoc(),
                  "cover has no fail statement; the else arm belongs to assert "
                  "and assume",
                  Subclause("16.3"));
    p.Expect(TokenKind::kKwElse, Subclause("16.3"));
    // Read the fail statement rather than leaving it, and discard it: §16.3
    // gives a cover nowhere to keep one, and Stmt::assert_fail_stmt stays null.
    p.ParseStmt();
  }
};

static void SkipBalancedPropertySpec(Lexer& lexer) {
  int depth = 1;
  while (depth > 0 && !lexer.Peek().Is(TokenKind::kEof)) {
    if (lexer.Peek().Is(TokenKind::kLParen)) {
      ++depth;
    } else if (lexer.Peek().Is(TokenKind::kRParen)) {
      --depth;
      if (depth == 0) break;
    }
    lexer.Next();
  }
}

// §16.14.6: a concurrent assertion statement embedded in procedural code is
// a pending instance of its property placed in the procedural assertion
// queue of the process that reaches it, evaluated as a separate concurrent
// assertion is once the instance matures, on the clocking event its spec
// opens with or, where it opens with none, on the clock the elaborator
// infers from the procedure, so the spec is read as the static statement's
// is, the clock optional: the events the spec opens with go to assert_clock
// and the body to the statement MakeSimplePropertyStmt makes, which the
// evaluation reads on §16.5.1's sampled values. A cover sequence stands
// beside the cover property. A spec of a form the static path does not read
// is reported and skipped.
Stmt* Parser::ParseProceduralConcurrentAssertLike(StmtKind kind) {
  auto* spec = arena_.Create<ModuleItem>();
  spec->loc = CurrentLoc();
  bool sequence = Match(TokenKind::kKwSequence);
  if (!sequence) Expect(TokenKind::kKwProperty, Subclause("16.14.6"));
  Expect(TokenKind::kLParen, Subclause("16.14.6"));
  Stmt* stmt = nullptr;
  if (TryParseSimpleConcurrentProperty(spec, kind)) {
    stmt = spec->body;
    stmt->assert_clock = spec->sensitivity;
  } else {
    stmt = arena_.Create<Stmt>();
    stmt->kind = kind;
    stmt->range.start = spec->loc;
    diag_.Warning(spec->loc,
                  "procedural concurrent assertion is not evaluated: its "
                  "property_spec holds more than the forms this tool "
                  "evaluates",
                  Subclause("16.14.6"));
    SkipBalancedPropertySpec(lexer_);
  }
  stmt->is_procedural_concurrent = true;
  stmt->cover_sequence = sequence;
  Expect(TokenKind::kRParen, Subclause("16.14.6"));

  ParserAssertHelpers::ParseActionBlock(*this, stmt);
  return stmt;
}

Stmt* Parser::ParseImmediateAssertLike(StmtKind kind, TokenKind keyword) {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = kind;
  stmt->range.start = CurrentLoc();
  Expect(keyword, Subclause("16.3"));

  if (Check(TokenKind::kKwProperty)) {
    return ParseProceduralConcurrentAssertLike(kind);
  }

  ParserAssertHelpers::ParseDeferral(*this, stmt);
  ParserAssertHelpers::ParseAssertedExpr(*this, stmt);
  ParserAssertHelpers::ParseActionBlock(*this, stmt);
  return stmt;
}

Stmt* Parser::ParseImmediateAssert() {
  return ParseImmediateAssertLike(StmtKind::kAssertImmediate,
                                  TokenKind::kKwAssert);
}

Stmt* Parser::ParseImmediateAssume() {
  return ParseImmediateAssertLike(StmtKind::kAssumeImmediate,
                                  TokenKind::kKwAssume);
}

Stmt* Parser::ParseImmediateCover() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kCoverImmediate;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwCover, Subclause("16.3"));

  if (Check(TokenKind::kKwProperty) || Check(TokenKind::kKwSequence)) {
    return ParseProceduralConcurrentAssertLike(StmtKind::kCoverImmediate);
  }

  ParserAssertHelpers::ParseDeferral(*this, stmt);
  ParserAssertHelpers::ParseAssertedExpr(*this, stmt);
  ParserAssertHelpers::ParseCoverTail(*this, stmt, Subclause("16.3"));

  return stmt;
}

static Expr* SkipPropertySpec(Arena& arena, Lexer& lexer, SourceLoc loc) {
  int depth = 1;
  while (depth > 0 && !lexer.Peek().Is(TokenKind::kEof)) {
    if (lexer.Peek().Is(TokenKind::kLParen)) {
      ++depth;
    } else if (lexer.Peek().Is(TokenKind::kRParen)) {
      --depth;
      if (depth == 0) break;
    }
    lexer.Next();
  }
  return ParserPropertySpecHelpers::PropertySpecPlaceholder(arena, loc);
}

static bool IsDeferredImmediate(Lexer& lexer) {
  if (lexer.Peek().Is(TokenKind::kHash)) return true;
  if (lexer.Peek().Is(TokenKind::kKwFinal)) return true;
  return false;
}

static ModuleItem* WrapStmtAsItem(Arena& arena, Stmt* stmt, SourceLoc loc) {
  auto* item = arena.Create<ModuleItem>();
  item->kind = ModuleItemKind::kAssertProperty;
  item->loc = loc;
  item->body = stmt;
  return item;
}

ModuleItem* Parser::ParseDeferredImmediateItem(SourceLoc loc, StmtKind kind) {
  ParserAssertHelpers::RejectDeferredInProgram(*this, loc);
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = kind;
  stmt->range.start = loc;
  stmt->is_deferred = true;
  ParserAssertHelpers::ParseDeferral(*this, stmt);
  ParserAssertHelpers::ParseAssertedExpr(*this, stmt);
  ParserAssertHelpers::ParseActionBlock(*this, stmt);
  return WrapStmtAsItem(arena_, stmt, loc);
}

// §16.14.5: a concurrent assertion used outside procedural code has `always`
// semantics. This captures the simple, non-temporal clocked form
// `@(event) boolean_expression` so the elaborator can model it as a clocked
// process: the leading clock is recorded in item->sensitivity and the boolean
// is wrapped as an immediate-assert body in item->body, which evaluates and
// reports at each clock edge. Any spec this cannot handle (no leading clock, or
// a temporal/sequence property) restores the lexer and returns false, leaving
// the caller to skip the spec as before. The trial parse is run with
// diagnostics suppressed so a discarded attempt never reports errors.

// Scan the property body (from the current token to the matching close
// parenthesis) for an operator that makes it a temporal/sequence property
// rather than a sampled boolean. ParseExpr already stops before sequence
// delays (##), repetition, and property keywords, but it *would* consume the
// implication operators |-> and |=>, so they must be detected here. The lexer
// position is left unchanged.
//
// The scan runs from the token after the leading clock when
// TryParseSimpleConcurrentProperty calls it, and from the first token of the
// property_spec when WarnUnevaluatedConcurrentAssertion does. Both are correct
// because the depth count treats the clocking event's own parentheses like any
// other pair: `@ ( posedge clk )` raises the depth to 1 and returns it to 0,
// leaving the scan to stop on the property_spec's own closing parenthesis.
// From the body of a named property declaration, where
// ParserPropertySpecHelpers::CapturePropertyTreeBody calls it, the scan stops
// at the semicolon ending the body, which stands at the same depth.

bool Parser::BodyHasTemporalOperator() {
  auto scan = lexer_.SavePos();
  int depth = 0;
  bool found = false;
  while (!Check(TokenKind::kEof)) {
    TokenKind k = CurrentToken().kind;
    if (k == TokenKind::kLParen) {
      ++depth;
    } else if (k == TokenKind::kRParen) {
      if (depth == 0) break;  // the property's own closing parenthesis
      --depth;
    } else if (k == TokenKind::kSemicolon && depth == 0) {
      break;  // the end of a named property's body
    } else if (k == TokenKind::kPipeDashGt || k == TokenKind::kPipeEqGt ||
               k == TokenKind::kHashHash) {
      found = true;
      break;
    }
    Consume();
  }
  lexer_.RestorePos(scan);
  return found;
}

// Reports that a concurrent assertion statement the source wrote will not be
// evaluated, naming which of the reasons below applies.
//
// §16.14 states the rule the report rests on: "A property on its own is never
// evaluated for checking an expression. It shall be used within an assertion
// statement (see 16.2) for this to occur." A source that writes one of the
// five concurrent assertion statements of Syntax 16-18 has asked for that
// evaluation. Every property_spec that cannot take the clocked-boolean path
// is handed to SkipPropertySpec and never lowered to a process, so
// Elaborator::ElaborateAssertPropertyItem in
// src/elaborator/elaborator_items_assertions.cpp finds no body and builds
// nothing. Without this report a design whose assertions were all discarded
// compiles exactly like one whose assertions all hold, and no line says which
// it was.
//
// This states a limit of this implementation and not a rule the source breaks,
// which is why it is a warning rather than an error, and why it is removable:
// #2923 makes assert and assume evaluate, and #2924 and #2927 add the property
// operators. Each branch below is deleted with the branch that discarded the
// form it names, and the whole function goes when the last of them does.
//
// Every caller stands at the first token of the property_spec, which is what
// lets BodyHasTemporalOperator and the '@' test read the spec this reports on:
// TryParseSimpleConcurrentProperty restores the lexer when it fails, and the
// cover and restrict statements never attempt it.
void Parser::WarnUnevaluatedConcurrentAssertion(SourceLoc loc) {
  // Named as §16.14 Syntax 16-18 writes the statement, so the report quotes
  // the source back rather than an internal enumerator name. An assert,
  // assume, cover property or cover sequence statement has the clocked
  // path, and one of the reasons below says why its spec missed it. A
  // restrict property never reaches here: §16.2 and §16.14.4 have a
  // simulator not check it, so its going unevaluated is the standard's rule
  // rather than this tool's gap.
  // The spec, with a clocking event or, §16.16 (a), without, was not read
  // into a body the evaluation reads; a spec with no clock at all is left to
  // the elaborator, which has the default clocking, so no reason here names
  // the clock.
  std::string reason;
  if (BodyHasTemporalOperator()) {
    // Reason one: the property is temporal and holds what the evaluation
    // does not read. #2924 and #2927 cover the operators.
    reason =
        "its property is temporal, using |->, |=> or ##, and this tool "
        "evaluates only a boolean property";
  } else {
    // Reason two: the boolean did not consume the rest of the spec.
    reason =
        "its property_spec holds more than the @(event) boolean_expression "
        "this tool evaluates";
  }
  diag_.Warning(loc, "concurrent assertion is not evaluated: " + reason,
                Subclause("16.14"));
}

// §16.12: `disable iff ( expression_or_dist )` may stand between the clock
// and the property_expr, making the spec a property_spec; `disable_iff`
// takes the condition where one is written and stays null otherwise. Answers
// false where the clause is malformed.
bool Parser::TryParseDisableIff(Expr*& disable_iff) {
  if (!Match(TokenKind::kKwDisable)) return true;
  if (!Match(TokenKind::kKwIff) || !Match(TokenKind::kLParen)) return false;
  disable_iff = ParserPropertySpecHelpers::ParseExpressionOrDist(*this);
  return disable_iff != nullptr && Match(TokenKind::kRParen);
}

// The clocking events are optional here, a procedural concurrent assertion
// taking its clock from the procedure (§16.14.6); a static statement's
// caller asks for the `@` before calling, its clock being the statement's
// own.
bool Parser::TryParseSimpleConcurrentProperty(ModuleItem* item,
                                              StmtKind body_kind) {
  auto saved = lexer_.SavePos();
  diag_.PushSuppress();
  std::vector<EventExpr> events;
  bool ok = true;
  // §16.13.3: of two clocking events juxtaposed the second nullifies the
  // first, so the last written is the spec's.
  while (ok && Match(TokenKind::kAt)) {
    events.clear();
    if (Match(TokenKind::kLParen)) {
      events = ParseEventList();
      if (!Match(TokenKind::kRParen)) ok = false;
    } else {
      events.push_back(ParseSingleEvent());
    }
  }
  SimpleSpecBody body;
  if (ok) ok = TryParseDisableIff(body.disable_iff);
  if (ok) ok = ParserPropertySpecHelpers::ParseSimpleSpecBody(*this, body);
  // Accept only what consumes the whole spec, so the next token is the
  // property's closing parenthesis. Anything else restores the lexer and the
  // caller skips the spec as before.
  if (!ok || !Check(TokenKind::kRParen)) {
    diag_.PopSuppress();
    lexer_.RestorePos(saved);
    return false;
  }
  diag_.PopSuppress();
  item->sensitivity = std::move(events);
  item->body = ParserPropertySpecHelpers::MakeSimplePropertyStmt(
      *this, item, body_kind, body);
  return true;
}

// §16.12.1: an instance of a named property can be used as a property_spec.
// A property_spec that is one name and nothing else is such an instance when
// the name is a property's, and the parser has no way to know whether it is:
// the declaration may come later in the module, and a variable's name reads
// the same. The name is recorded in prop_instance_name for
// Elaborator::ElaborateAssertPropertyItem, which substitutes the property's
// body when it is the clocked boolean form and reports the assertion
// unevaluated otherwise, so the parser reports nothing here. A spec of any
// other shape leaves the lexer where it was and answers false.
// §16.16 (b): an instance of a property or sequence declared in a clocking
// block is named through the block, `posedge_clk.q4`, which the expression
// parse reads as a member access; it is made the one identifier the
// registry keys the declaration under.
static Expr* QualifiedInstanceName(Expr* instance, Arena& arena) {
  if (instance == nullptr || instance->kind != ExprKind::kMemberAccess ||
      instance->is_scope_resolution || instance->lhs == nullptr ||
      instance->rhs == nullptr ||
      instance->lhs->kind != ExprKind::kIdentifier ||
      instance->rhs->kind != ExprKind::kIdentifier) {
    return instance;
  }
  auto* qualified =
      arena.Create<std::string>(std::string(instance->lhs->text) + "." +
                                std::string(instance->rhs->text));
  instance->kind = ExprKind::kIdentifier;
  instance->text = *qualified;
  instance->lhs = nullptr;
  instance->rhs = nullptr;
  return instance;
}

bool Parser::TryParsePropertyInstanceSpec(ModuleItem* item) {
  if (!Check(TokenKind::kIdentifier)) return false;
  auto saved = lexer_.SavePos();
  diag_.PushSuppress();
  // §16.12: an instance may carry actual arguments, `p(a, b)`, read as a
  // call is; the elaborator binds them to the property's formals. §16.12.18:
  // an actual that is a sequence, a property or an event expression is read
  // by the instance parse, since no expression holds one.
  Expr* instance = ParserPropertySpecHelpers::TryParsePropertyInstance(*this);
  if (instance == nullptr) instance = ParseExpr();
  diag_.PopSuppress();
  instance = QualifiedInstanceName(instance, arena_);
  bool is_instance = instance != nullptr && Check(TokenKind::kRParen) &&
                     (instance->kind == ExprKind::kIdentifier ||
                      instance->kind == ExprKind::kCall);
  if (!is_instance) {
    lexer_.RestorePos(saved);
    return false;
  }
  item->prop_instance_name =
      instance->kind == ExprKind::kCall ? instance->callee : instance->text;
  item->assert_expr = instance;
  return true;
}

// §16.16: the property_spec of a static concurrent assertion statement, in
// the forms the evaluation reads: one opening with a clocking event, (d)
// the statement's own; one that is an instance of a named property or
// sequence, recorded for the elaborator, which (f) determines the clock from
// the declaration; and, §16.16 (a), one opening with none, whose leading
// clocking event the elaborator takes from the default clocking. Answers
// whether the spec was read into a body; an instance answers false with
// prop_instance_name set.
bool Parser::ReadStaticPropertySpec(ModuleItem* item, StmtKind body_kind) {
  if (Check(TokenKind::kAt)) {
    return TryParseSimpleConcurrentProperty(item, body_kind);
  }
  if (TryParsePropertyInstanceSpec(item)) return false;
  return TryParseSimpleConcurrentProperty(item, body_kind);
}

ModuleItem* Parser::ParsePropertyAssertLike(ModuleItemKind kind,
                                            TokenKind keyword) {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = kind;
  item->loc = CurrentLoc();
  Expect(keyword, Subclause("16.14"));

  if (IsDeferredImmediate(lexer_)) {
    StmtKind sk = (kind == ModuleItemKind::kAssertProperty)
                      ? StmtKind::kAssertImmediate
                      : StmtKind::kAssumeImmediate;
    return ParseDeferredImmediateItem(item->loc, sk);
  }

  Expect(TokenKind::kKwProperty, Subclause("16.14"));
  Expect(TokenKind::kLParen, Subclause("16.14"));
  // Annex F.5.3.1 defines an assume property statement's satisfaction as the
  // assert property statement's, and §16.14.2 has a simulator check an
  // assumption as it checks an assertion, so the clocked boolean form is read
  // for both; the body's kind keeps the directive for §20.11's controls.
  StmtKind body_kind = kind == ModuleItemKind::kAssertProperty
                           ? StmtKind::kAssertImmediate
                           : StmtKind::kAssumeImmediate;
  bool simple_concurrent = ReadStaticPropertySpec(item, body_kind);
  if (!simple_concurrent && item->prop_instance_name.empty()) {
    // Before SkipPropertySpec, which moves the lexer off the property_spec the
    // reason is read from.
    WarnUnevaluatedConcurrentAssertion(item->loc);
    item->assert_expr = SkipPropertySpec(arena_, lexer_, CurrentLoc());
  }
  Expect(TokenKind::kRParen, Subclause("16.14"));

  if (!Check(TokenKind::kSemicolon) && !Check(TokenKind::kKwElse)) {
    item->assert_pass_stmt = ParseStmt();
  }
  if (Match(TokenKind::kKwElse)) {
    item->assert_fail_stmt = ParseStmt();
  }
  if (!item->assert_pass_stmt && !item->assert_fail_stmt) {
    Expect(TokenKind::kSemicolon, Subclause("16.14"));
  }
  // For the clocked simple form the action block belongs to the synthesized
  // assert body that the elaborator lowers (item->assert_* is otherwise unread
  // for a concurrent assert property).
  if (simple_concurrent) {
    item->body->assert_pass_stmt = item->assert_pass_stmt;
    item->body->assert_fail_stmt = item->assert_fail_stmt;
  }
  return item;
}

ModuleItem* Parser::ParseAssertProperty() {
  return ParsePropertyAssertLike(ModuleItemKind::kAssertProperty,
                                 TokenKind::kKwAssert);
}

ModuleItem* Parser::ParseAssumeProperty() {
  return ParsePropertyAssertLike(ModuleItemKind::kAssumeProperty,
                                 TokenKind::kKwAssume);
}

ModuleItem* Parser::ParseCoverProperty() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kCoverProperty;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwCover, Subclause("16.14.3"));

  if (IsDeferredImmediate(lexer_)) {
    // The deferred cover is read here rather than through
    // ParseDeferredImmediateItem, its tail being a cover's.
    ParserAssertHelpers::RejectDeferredInProgram(*this, item->loc);
    auto* stmt = arena_.Create<Stmt>();
    stmt->kind = StmtKind::kCoverImmediate;
    stmt->range.start = item->loc;
    stmt->is_deferred = true;
    if (Match(TokenKind::kHash)) {
      auto tok = Expect(TokenKind::kIntLiteral, Subclause("16.4"));

      ExpectDeferredHashZero(diag_, tok);
    } else if (Match(TokenKind::kKwFinal)) {
      stmt->is_final_deferred = true;
    }
    Expect(TokenKind::kLParen, Subclause("16.4"));
    stmt->assert_expr = ParseExpr();
    Expect(TokenKind::kRParen, Subclause("16.4"));
    ParserAssertHelpers::ParseCoverTail(*this, stmt, Subclause("16.4"));
    return WrapStmtAsItem(arena_, stmt, item->loc);
  }

  if (Check(TokenKind::kKwSequence)) {
    item->kind = ModuleItemKind::kCoverSequence;
    Expect(TokenKind::kKwSequence, Subclause("16.14.3"));
  } else {
    Expect(TokenKind::kKwProperty, Subclause("16.14.3"));
  }

  Expect(TokenKind::kLParen, Subclause("16.14.3"));
  // Annex F.5.3.1 defines a cover property statement's satisfaction over the
  // same words as an assert property statement's, and §16.14.3 runs its pass
  // statement once per successful evaluation, so the clocked boolean form is
  // read as ParsePropertyAssertLike reads it, with a cover body so the
  // evaluation reports nothing where the property does not hold. §16.14 lists
  // cover_sequence_statement beside it, whose spec is a sequence_expr under
  // a clocking event and a disable condition, read as the same spec is and
  // covered at every match of the sequence, which the body is marked for; a
  // cover whose spec is an instance of a named property or sequence, §16.12.1
  // and §16.14, is recorded for the elaborator as ParsePropertyAssertLike
  // records one, and a cover whose spec is neither has its spec skipped.
  bool simple_concurrent =
      ReadStaticPropertySpec(item, StmtKind::kCoverImmediate);
  if (!simple_concurrent && item->prop_instance_name.empty()) {
    WarnUnevaluatedConcurrentAssertion(item->loc);
    item->assert_expr = SkipPropertySpec(arena_, lexer_, CurrentLoc());
  }
  Expect(TokenKind::kRParen, Subclause("16.14.3"));

  if (!Check(TokenKind::kSemicolon)) {
    item->assert_pass_stmt = ParseStmt();
  } else {
    Expect(TokenKind::kSemicolon, Subclause("16.14.3"));
  }
  if (simple_concurrent) {
    item->body->assert_pass_stmt = item->assert_pass_stmt;
    item->body->cover_sequence = item->kind == ModuleItemKind::kCoverSequence;
  }
  return item;
}

// §16.14: the keywords a concurrent_assertion_statement opens with.
static bool IsConcurrentAssertionKeyword(TokenKind kind) {
  return kind == TokenKind::kKwAssert || kind == TokenKind::kKwAssume ||
         kind == TokenKind::kKwCover || kind == TokenKind::kKwRestrict;
}

// The keyword alone decides nothing, an always procedure whose body is an
// immediate or a deferred assertion being a procedure; the property or
// sequence keyword after it does. The `;` the assert form ends with is a
// null module item, and an assume, a cover sequence and a restrict under
// always are read as the assert and the cover are.
ModuleItem* ParserPropertySpecHelpers::TryParseAlwaysConcurrentAssertion(
    Parser& p) {
  if (!IsConcurrentAssertionKeyword(p.CurrentToken().kind)) return nullptr;
  auto saved = p.lexer_.SavePos();
  TokenKind keyword = p.Consume().kind;
  bool is_concurrent =
      p.Check(TokenKind::kKwProperty) || p.Check(TokenKind::kKwSequence);
  p.lexer_.RestorePos(saved);
  if (!is_concurrent) return nullptr;
  switch (keyword) {
    case TokenKind::kKwAssert:
      return p.ParseAssertProperty();
    case TokenKind::kKwAssume:
      return p.ParseAssumeProperty();
    case TokenKind::kKwCover:
      return p.ParseCoverProperty();
    default:
      return p.ParseRestrictProperty();
  }
}

ModuleItem* Parser::ParseRestrictProperty() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kRestrictProperty;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwRestrict, Subclause("16.14.4"));
  Expect(TokenKind::kKwProperty, Subclause("16.14.4"));
  Expect(TokenKind::kLParen, Subclause("16.14.4"));
  // §16.2 has a simulator not check a restrict property, and §16.14.4 says the
  // statement is not verified in simulation, so its spec is skipped without
  // the §16.14 non-evaluation report the other concurrent assertions draw
  // when this tool cannot evaluate them: here, not evaluating is the rule.
  item->assert_expr = SkipPropertySpec(arena_, lexer_, CurrentLoc());
  Expect(TokenKind::kRParen, Subclause("16.14.4"));
  Expect(TokenKind::kSemicolon, Subclause("16.14.4"));
  return item;
}

Stmt* Parser::ParseExpectStmt() {
  auto* stmt = arena_.Create<Stmt>();

  stmt->kind = StmtKind::kExpect;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwExpect, Subclause("16.17"));
  Expect(TokenKind::kLParen, Subclause("16.17"));

  int depth = 1;
  while (depth > 0 && !AtEnd()) {
    if (Match(TokenKind::kLParen)) {
      ++depth;
    } else if (Match(TokenKind::kRParen)) {
      --depth;
    } else {
      Consume();
    }
  }

  if (!Check(TokenKind::kSemicolon) && !Check(TokenKind::kKwElse)) {
    stmt->assert_pass_stmt = ParseStmt();
  }
  if (Match(TokenKind::kKwElse)) stmt->assert_fail_stmt = ParseStmt();
  if (!stmt->assert_pass_stmt && !stmt->assert_fail_stmt) {
    Expect(TokenKind::kSemicolon, Subclause("16.17"));
  }
  stmt->range.end = CurrentLoc();
  return stmt;
}

}  // namespace delta
