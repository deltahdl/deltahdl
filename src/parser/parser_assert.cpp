#include "parser/parser.h"

namespace delta {

static void ExpectDeferredHashZero(DiagEngine& diag, const Token& tok) {
  if (tok.text != "0") {
    diag.Error(tok.loc, "deferred immediate assertion requires #0, got #" +
                            std::string(tok.text));
  }
}

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
  Expect(TokenKind::kKwProperty);
  Expect(TokenKind::kLParen);
  stmt->assert_expr = nullptr;
  SkipBalancedPropertySpec(lexer_);
  Expect(TokenKind::kRParen);

  if (!Check(TokenKind::kSemicolon) && !Check(TokenKind::kKwElse)) {
    stmt->assert_pass_stmt = ParseStmt();
  }
  if (Match(TokenKind::kKwElse)) {
    stmt->assert_fail_stmt = ParseStmt();
  }
  if (!stmt->assert_pass_stmt && !stmt->assert_fail_stmt) {
    Expect(TokenKind::kSemicolon);
  }
  return stmt;
}

Stmt* Parser::ParseImmediateAssertLike(StmtKind kind, TokenKind keyword) {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = kind;
  stmt->range.start = CurrentLoc();
  Expect(keyword);

  if (Check(TokenKind::kKwProperty)) {
    return ParseProceduralConcurrentAssertLike(kind);
  }

  if (Match(TokenKind::kHash)) {
    auto tok = Expect(TokenKind::kIntLiteral);
    ExpectDeferredHashZero(diag_, tok);
    stmt->is_deferred = true;
  } else if (Match(TokenKind::kKwFinal)) {
    stmt->is_deferred = true;
    stmt->is_final_deferred = true;
  }

  Expect(TokenKind::kLParen);
  stmt->assert_expr = ParseExpr();
  Expect(TokenKind::kRParen);

  if (!Check(TokenKind::kSemicolon) && !Check(TokenKind::kKwElse)) {
    stmt->assert_pass_stmt = ParseStmt();
  }
  if (Match(TokenKind::kKwElse)) {
    stmt->assert_fail_stmt = ParseStmt();
  }
  if (!stmt->assert_pass_stmt && !stmt->assert_fail_stmt) {
    Expect(TokenKind::kSemicolon);
  }

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
  Expect(TokenKind::kKwCover);

  if (Check(TokenKind::kKwProperty)) {
    return ParseProceduralConcurrentAssertLike(StmtKind::kCoverImmediate);
  }

  if (Match(TokenKind::kHash)) {
    auto tok = Expect(TokenKind::kIntLiteral);
    ExpectDeferredHashZero(diag_, tok);
    stmt->is_deferred = true;
  } else if (Match(TokenKind::kKwFinal)) {
    stmt->is_deferred = true;
    stmt->is_final_deferred = true;
  }

  Expect(TokenKind::kLParen);
  stmt->assert_expr = ParseExpr();
  Expect(TokenKind::kRParen);

  if (!Check(TokenKind::kSemicolon)) {
    stmt->assert_pass_stmt = ParseStmt();
  } else {
    Expect(TokenKind::kSemicolon);
  }

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
  if (Match(TokenKind::kHash)) {
    auto tok = Expect(TokenKind::kIntLiteral);

    ExpectDeferredHashZero(diag_, tok);
  } else if (Match(TokenKind::kKwFinal)) {
    stmt->is_final_deferred = true;
  }
  Expect(TokenKind::kLParen);
  stmt->assert_expr = ParseExpr();
  Expect(TokenKind::kRParen);
  if (!Check(TokenKind::kSemicolon) && !Check(TokenKind::kKwElse)) {
    stmt->assert_pass_stmt = ParseStmt();
  }
  if (Match(TokenKind::kKwElse)) stmt->assert_fail_stmt = ParseStmt();
  if (!stmt->assert_pass_stmt && !stmt->assert_fail_stmt) {
    Expect(TokenKind::kSemicolon);
  }
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
// Scan the property body (from the token after the leading clock to the
// matching close parenthesis) for an operator that makes it a temporal/sequence
// property rather than a sampled boolean. ParseExpr already stops before
// sequence delays (##), repetition, and property keywords, but it *would*
// consume the implication operators |-> and |=>, so they must be detected here.
// The lexer position is left unchanged.
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
  Expect(keyword);

  if (IsDeferredImmediate(lexer_)) {
    StmtKind sk = (kind == ModuleItemKind::kAssertProperty)
                      ? StmtKind::kAssertImmediate
                      : StmtKind::kAssumeImmediate;
    return ParseDeferredImmediateItem(item->loc, sk);
  }

  Expect(TokenKind::kKwProperty);
  Expect(TokenKind::kLParen);
  bool simple_concurrent = kind == ModuleItemKind::kAssertProperty &&
                           TryParseSimpleConcurrentProperty(item);
  if (!simple_concurrent) {
    item->assert_expr = SkipPropertySpec(arena_, lexer_, CurrentLoc());
  }
  Expect(TokenKind::kRParen);

  if (!Check(TokenKind::kSemicolon) && !Check(TokenKind::kKwElse)) {
    item->assert_pass_stmt = ParseStmt();
  }
  if (Match(TokenKind::kKwElse)) {
    item->assert_fail_stmt = ParseStmt();
  }
  if (!item->assert_pass_stmt && !item->assert_fail_stmt) {
    Expect(TokenKind::kSemicolon);
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
  Expect(TokenKind::kKwCover);

  if (IsDeferredImmediate(lexer_)) {
    auto* stmt = arena_.Create<Stmt>();
    stmt->kind = StmtKind::kCoverImmediate;
    stmt->range.start = item->loc;
    stmt->is_deferred = true;
    if (Match(TokenKind::kHash)) {
      auto tok = Expect(TokenKind::kIntLiteral);

      ExpectDeferredHashZero(diag_, tok);
    } else if (Match(TokenKind::kKwFinal)) {
      stmt->is_final_deferred = true;
    }
    Expect(TokenKind::kLParen);
    stmt->assert_expr = ParseExpr();
    Expect(TokenKind::kRParen);
    if (!Check(TokenKind::kSemicolon)) {
      stmt->assert_pass_stmt = ParseStmt();
    } else {
      Expect(TokenKind::kSemicolon);
    }
    return WrapStmtAsItem(arena_, stmt, item->loc);
  }

  if (Check(TokenKind::kKwSequence)) {
    item->kind = ModuleItemKind::kCoverSequence;
    Expect(TokenKind::kKwSequence);
  } else {
    Expect(TokenKind::kKwProperty);
  }

  Expect(TokenKind::kLParen);
  item->assert_expr = SkipPropertySpec(arena_, lexer_, CurrentLoc());
  Expect(TokenKind::kRParen);

  if (!Check(TokenKind::kSemicolon)) {
    item->assert_pass_stmt = ParseStmt();
  } else {
    Expect(TokenKind::kSemicolon);
  }
  return item;
}

ModuleItem* Parser::ParseRestrictProperty() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kRestrictProperty;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwRestrict);
  Expect(TokenKind::kKwProperty);
  Expect(TokenKind::kLParen);
  item->assert_expr = SkipPropertySpec(arena_, lexer_, CurrentLoc());
  Expect(TokenKind::kRParen);
  Expect(TokenKind::kSemicolon);
  return item;
}

Stmt* Parser::ParseExpectStmt() {
  auto* stmt = arena_.Create<Stmt>();

  stmt->kind = StmtKind::kExpect;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwExpect);
  Expect(TokenKind::kLParen);

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
    Expect(TokenKind::kSemicolon);
  }
  stmt->range.end = CurrentLoc();
  return stmt;
}

}  // namespace delta
