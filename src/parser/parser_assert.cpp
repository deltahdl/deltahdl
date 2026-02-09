#include "parser/parser.h"

namespace delta {

// =============================================================================
// §16.3 Immediate assertions
// =============================================================================

// Shared logic for immediate assert/assume (§16.3).
Stmt* Parser::ParseImmediateAssertLike(StmtKind kind, TokenKind keyword) {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = kind;
  stmt->range.start = CurrentLoc();
  Expect(keyword);

  if (Match(TokenKind::kHash)) {
    Expect(TokenKind::kIntLiteral);
    stmt->is_deferred = true;
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

// Parse: cover [#0] (expr) [pass_stmt] ;
// Note: cover has no else branch per the LRM.
Stmt* Parser::ParseImmediateCover() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kCoverImmediate;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwCover);

  if (Match(TokenKind::kHash)) {
    Expect(TokenKind::kIntLiteral);
    stmt->is_deferred = true;
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

// =============================================================================
// §16.5 Concurrent assertions — module-level items
// =============================================================================

// Skip a balanced parenthesised property_spec body. SVA property_spec may
// contain timing controls (@), implication operators (|->, |=>), cycle
// delays (##), and constructs outside the regular expression grammar.
// Returns a placeholder identifier so the AST node is non-null.
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

// Shared logic for assert/assume property (§16.5).
ModuleItem* Parser::ParsePropertyAssertLike(ModuleItemKind kind,
                                            TokenKind keyword) {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = kind;
  item->loc = CurrentLoc();
  Expect(keyword);
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

// Parse: cover property ( property_spec ) [pass_stmt] ;
ModuleItem* Parser::ParseCoverProperty() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kCoverProperty;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwCover);
  Expect(TokenKind::kKwProperty);
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

// =============================================================================
// §16.12 Property declarations
// =============================================================================

// Parse: property name [( port_list )]; ... endproperty [: name]
ModuleItem* Parser::ParsePropertyDecl() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kPropertyDecl;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwProperty);
  item->name = Expect(TokenKind::kIdentifier).text;

  // Optional formal port list.
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

  // Skip property body until endproperty.
  while (!Check(TokenKind::kKwEndproperty) && !AtEnd()) {
    Consume();
  }
  Expect(TokenKind::kKwEndproperty);
  if (Match(TokenKind::kColon)) ExpectIdentifier();
  return item;
}

// =============================================================================
// §16.8 Sequence declarations
// =============================================================================

// Parse: sequence name [( port_list )]; ... endsequence [: name]
ModuleItem* Parser::ParseSequenceDecl() {
  auto* item = arena_.Create<ModuleItem>();
  item->kind = ModuleItemKind::kSequenceDecl;
  item->loc = CurrentLoc();
  Expect(TokenKind::kKwSequence);
  item->name = Expect(TokenKind::kIdentifier).text;

  // Optional formal port list.
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

  // Skip sequence body until endsequence.
  while (!Check(TokenKind::kKwEndsequence) && !AtEnd()) {
    Consume();
  }
  Expect(TokenKind::kKwEndsequence);
  if (Match(TokenKind::kColon)) ExpectIdentifier();
  return item;
}

}  // namespace delta
