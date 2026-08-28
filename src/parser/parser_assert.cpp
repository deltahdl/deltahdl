#include "parser/parser.h"

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

Stmt* Parser::ParseProceduralConcurrentAssertLike(StmtKind kind) {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = kind;
  stmt->range.start = CurrentLoc();

  stmt->is_procedural_concurrent = true;
  Expect(TokenKind::kKwProperty, Subclause("16.14.6"));
  Expect(TokenKind::kLParen, Subclause("16.14.6"));
  stmt->assert_expr = nullptr;
  SkipBalancedPropertySpec(lexer_);
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

  if (Check(TokenKind::kKwProperty)) {
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
  auto* expr = arena.Create<Expr>();
  expr->kind = ExprKind::kIdentifier;
  expr->text = "<property_spec>";
  expr->range.start = loc;
  return expr;
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
void Parser::WarnUnevaluatedConcurrentAssertion(SourceLoc loc,
                                                ModuleItemKind kind) {
  // Named as §16.14 Syntax 16-18 writes the statement, so the report quotes
  // the source back rather than an internal enumerator name.
  std::string_view directive;
  if (kind == ModuleItemKind::kAssumeProperty) {
    directive = "assume property";
  } else if (kind == ModuleItemKind::kCoverProperty) {
    directive = "cover property";
  } else if (kind == ModuleItemKind::kCoverSequence) {
    directive = "cover sequence";
  } else if (kind == ModuleItemKind::kRestrictProperty) {
    directive = "restrict property";
  }

  std::string reason;
  if (!directive.empty()) {
    // Reason one: the statement is not `assert property`, and no other
    // directive has an evaluation path at all, whatever its property_spec
    // holds. #2923 covers assume.
    reason = std::string(directive) +
             " is parsed and then discarded, this tool evaluating only "
             "assert property";
  } else if (BodyHasTemporalOperator()) {
    // Reason two: the property is temporal, so it is not the sampled boolean
    // TryParseSimpleConcurrentProperty lowers. #2924 and #2927 cover the
    // operators.
    reason =
        "its property is temporal, using |->, |=> or ##, and this tool "
        "evaluates only a boolean property";
  } else if (!Check(TokenKind::kAt)) {
    // Reason three: an assert property whose property_spec does not open with
    // a clocking event. §16.14.5 allows the clock to be inferred, which this
    // tool does not do, so there is nothing to sample the boolean on.
    reason =
        "its property_spec has no leading clocking event, and this tool "
        "evaluates only the clocked form @(event) boolean_expression";
  } else {
    // Reason three by its other route: the spec opens with a clocking event
    // but the boolean did not consume the rest of it.
    reason =
        "its property_spec holds more than the @(event) boolean_expression "
        "this tool evaluates";
  }

  diag_.Warning(loc, "concurrent assertion is not evaluated: " + reason,
                Subclause("16.14"));
}

bool Parser::TryParseSimpleConcurrentProperty(ModuleItem* item) {
  if (!Check(TokenKind::kAt)) return false;
  auto saved = lexer_.SavePos();
  diag_.PushSuppress();
  Consume();  // '@'
  std::vector<EventExpr> events;
  bool ok = true;
  if (Match(TokenKind::kLParen)) {
    events = ParseEventList();
    if (!Match(TokenKind::kRParen)) ok = false;
  } else {
    events.push_back(ParseSingleEvent());
  }
  bool temporal = ok && BodyHasTemporalOperator();
  Expr* prop = (ok && !temporal) ? ParseExpr() : nullptr;
  // Accept only the simple form: a non-temporal boolean that consumes the whole
  // spec, so the next token is the property's closing parenthesis. Anything
  // else restores the lexer and the caller skips the spec as before.
  if (!ok || temporal || !Check(TokenKind::kRParen)) {
    diag_.PopSuppress();
    lexer_.RestorePos(saved);
    return false;
  }
  diag_.PopSuppress();
  item->sensitivity = std::move(events);
  item->assert_expr = prop;
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kAssertImmediate;
  stmt->range.start = item->loc;
  stmt->assert_expr = prop;
  item->body = stmt;
  return true;
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
  bool simple_concurrent = kind == ModuleItemKind::kAssertProperty &&
                           TryParseSimpleConcurrentProperty(item);
  if (!simple_concurrent) {
    // Before SkipPropertySpec, which moves the lexer off the property_spec the
    // reason is read from.
    WarnUnevaluatedConcurrentAssertion(item->loc, kind);
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
  // §16.14 lists cover_property_statement and cover_sequence_statement among
  // the concurrent assertion statements, and neither reaches the
  // clocked-boolean path in ParsePropertyAssertLike: both skip the spec here.
  WarnUnevaluatedConcurrentAssertion(item->loc, item->kind);
  item->assert_expr = SkipPropertySpec(arena_, lexer_, CurrentLoc());
  Expect(TokenKind::kRParen, Subclause("16.14.3"));

  if (!Check(TokenKind::kSemicolon)) {
    item->assert_pass_stmt = ParseStmt();
  } else {
    Expect(TokenKind::kSemicolon, Subclause("16.14.3"));
  }
  return item;
}

ModuleItem* Parser::ParseRestrictProperty() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kRestrictProperty;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwRestrict, Subclause("16.14.4"));
  Expect(TokenKind::kKwProperty, Subclause("16.14.4"));
  Expect(TokenKind::kLParen, Subclause("16.14.4"));
  // §16.14 lists restrict_property_statement among the concurrent assertion
  // statements too, and it likewise only ever skips its spec.
  WarnUnevaluatedConcurrentAssertion(item->loc, item->kind);
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
