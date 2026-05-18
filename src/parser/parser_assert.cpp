#include "parser/parser.h"

namespace delta {

static void ExpectDeferredHashZero(DiagEngine& diag, const Token& tok) {
  if (tok.text != "0") {
    diag.Error(tok.loc,
               "deferred immediate assertion requires #0, got #" +
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
  item->assert_expr = SkipPropertySpec(arena_, lexer_, CurrentLoc());
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

// §16.12 + §F.4.1: capture formal names, body disable-iff count, and nested
// property/sequence instance references so the rewriter has what it needs.
ModuleItem* Parser::ParsePropertyDecl() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kPropertyDecl;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwProperty);
  item->name = Expect(TokenKind::kIdentifier).text;

  if (Match(TokenKind::kLParen)) {
    int depth = 1;
    bool expect_formal_name = true;
    bool saw_local = false;
    while (depth > 0 && !AtEnd()) {
      if (Check(TokenKind::kLParen)) {
        Consume();
        ++depth;
      } else if (Check(TokenKind::kRParen)) {
        Consume();
        --depth;
        if (depth == 0) break;
      } else if (depth == 1 && Check(TokenKind::kComma)) {
        Consume();
        expect_formal_name = true;
        saw_local = false;
      } else if (depth == 1 && Check(TokenKind::kEq)) {
        Consume();
        expect_formal_name = false;
      } else if (depth == 1 && Check(TokenKind::kKwLocal)) {
        Consume();
        saw_local = true;
      } else if (depth == 1 &&
                 (Check(TokenKind::kKwOutput) ||
                  Check(TokenKind::kKwInout))) {
        // property_lvar_port_direction is restricted to `input` only;
        // `output` and `inout` have no legal role inside a property port,
        // with or without a preceding `local`.
        diag_.Error(CurrentLoc(),
                    "property port direction must be 'input'");
        Consume();
        saw_local = false;
      } else if (depth == 1 && Check(TokenKind::kKwInput)) {
        // `input` is permitted only after `local`.
        if (!saw_local) {
          diag_.Error(CurrentLoc(),
                      "property port direction 'input' requires 'local'");
        }
        Consume();
        saw_local = false;
      } else if (expect_formal_name && depth == 1 &&
                 Check(TokenKind::kIdentifier)) {
        auto name_tok = Consume();
        if (!Check(TokenKind::kComma) && !Check(TokenKind::kRParen) &&
            !Check(TokenKind::kEq)) {
          if (Check(TokenKind::kIdentifier)) {
            name_tok = Consume();
          }
        }
        item->prop_formals.push_back(name_tok.text);
        expect_formal_name = false;
        saw_local = false;
      } else {
        Consume();
      }
    }
  }

  Expect(TokenKind::kSemicolon);

  while (!Check(TokenKind::kKwEndproperty) && !AtEnd()) {
    if (Check(TokenKind::kKwDisable)) {
      Consume();
      if (Check(TokenKind::kKwIff)) {
        Consume();
        ++item->prop_disable_iff_count;
      }
      continue;
    }
    if (Check(TokenKind::kIdentifier)) {
      auto tok = Consume();
      if (Check(TokenKind::kLParen)) {
        item->prop_instance_refs.push_back(tok.text);
      }
      continue;
    }
    Consume();
  }
  Expect(TokenKind::kKwEndproperty);
  MatchEndLabel(item->name);
  return item;
}

ModuleItem* Parser::ParseSequenceDecl() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kSequenceDecl;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwSequence);
  item->name = Expect(TokenKind::kIdentifier).text;

  if (Match(TokenKind::kLParen)) {
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
  }

  Expect(TokenKind::kSemicolon);

  while (!Check(TokenKind::kKwEndsequence) && !AtEnd()) {
    Consume();
  }
  Expect(TokenKind::kKwEndsequence);
  MatchEndLabel(item->name);
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

}
