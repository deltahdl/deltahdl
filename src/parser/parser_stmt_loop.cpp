// The loop statements of IEEE 1800-2023 §12.7 other than for: while, forever,
// repeat, foreach and do-while. The for statement stays in parser_stmt.cpp
// because it reads its initialisers through ParserStmtHelpers, which is
// file-local to that translation unit. The split keeps both files inside the
// 1000-line limit assert-no-oversized-source-files enforces.

#include "parser/parser.h"

namespace delta {

Stmt* Parser::ParseWhileStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kWhile;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwWhile, Subclause::Unread());
  Expect(TokenKind::kLParen, Subclause::Unread());
  stmt->condition = ParseExpr();
  Expect(TokenKind::kRParen, Subclause::Unread());
  stmt->body = ParseStmt();
  return stmt;
}

Stmt* Parser::ParseForeverStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kForever;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwForever, Subclause::Unread());
  stmt->body = ParseStmt();
  return stmt;
}

Stmt* Parser::ParseRepeatStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kRepeat;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwRepeat, Subclause::Unread());
  Expect(TokenKind::kLParen, Subclause::Unread());
  stmt->condition = ParseExpr();
  Expect(TokenKind::kRParen, Subclause::Unread());
  stmt->body = ParseStmt();
  return stmt;
}

Expr* Parser::ParseForeachArrayId() {
  auto* expr = arena_.Create<Expr>();
  expr->kind = ExprKind::kIdentifier;
  expr->range.start = CurrentLoc();
  expr->text = ExpectIdentifier(Subclause::Unread()).text;

  while (Check(TokenKind::kDot) && !AtEnd()) {
    Consume();
    auto* mem = arena_.Create<Expr>();
    mem->kind = ExprKind::kMemberAccess;
    mem->lhs = expr;
    mem->text = ExpectIdentifier(Subclause::Unread()).text;
    expr = mem;
  }
  return expr;
}

Stmt* Parser::ParseForeachStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kForeach;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwForeach, Subclause::Unread());
  Expect(TokenKind::kLParen, Subclause::Unread());

  stmt->expr = ParseForeachArrayId();
  Expect(TokenKind::kLBracket, Subclause::Unread());
  ParseForeachVars(stmt->foreach_vars);
  Expect(TokenKind::kRBracket, Subclause::Unread());
  Expect(TokenKind::kRParen, Subclause::Unread());
  stmt->body = ParseStmt();
  return stmt;
}

void Parser::ParseForeachVars(std::vector<std::string_view>& vars) {
  if (CheckIdentifier()) {
    vars.push_back(Consume().text);
  } else {
    vars.emplace_back();
  }
  while (Match(TokenKind::kComma)) {
    if (CheckIdentifier()) {
      vars.push_back(Consume().text);
    } else {
      vars.emplace_back();
    }
  }
}

Stmt* Parser::ParseDoWhileStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kDoWhile;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwDo, Subclause::Unread());
  stmt->body = ParseStmt();
  Expect(TokenKind::kKwWhile, Subclause::Unread());
  Expect(TokenKind::kLParen, Subclause::Unread());
  stmt->condition = ParseExpr();
  Expect(TokenKind::kRParen, Subclause::Unread());
  Expect(TokenKind::kSemicolon, Subclause::Unread());
  return stmt;
}

}  // namespace delta
