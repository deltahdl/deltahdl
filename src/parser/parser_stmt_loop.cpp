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
  Expect(TokenKind::kKwWhile, Subclause("12.7.4"));
  Expect(TokenKind::kLParen, Subclause("12.7.4"));
  stmt->condition = ParseExpr();
  Expect(TokenKind::kRParen, Subclause("12.7.4"));
  stmt->body = ParseStmt();
  return stmt;
}

Stmt* Parser::ParseForeverStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kForever;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwForever, Subclause("12.7.6"));
  stmt->body = ParseStmt();
  return stmt;
}

Stmt* Parser::ParseRepeatStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kRepeat;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwRepeat, Subclause("12.7.2"));
  Expect(TokenKind::kLParen, Subclause("12.7.2"));
  stmt->condition = ParseExpr();
  Expect(TokenKind::kRParen, Subclause("12.7.2"));
  stmt->body = ParseStmt();
  return stmt;
}

Expr* Parser::ParseForeachArrayId() {
  auto* expr = arena_.Create<Expr>();
  expr->kind = ExprKind::kIdentifier;
  expr->range.start = CurrentLoc();
  expr->text = ExpectIdentifier(Subclause("12.7.3")).text;

  while (Check(TokenKind::kDot) && !AtEnd()) {
    Consume();
    auto* mem = arena_.Create<Expr>();
    mem->kind = ExprKind::kMemberAccess;
    // §12.7.3 writes the array identifier as its own name followed by the
    // member names, so it begins where the name at the bottom does, which is
    // what Parser::MakeMemberAccess does for a dotted name in an expression.
    mem->range.start = expr->range.start;
    mem->lhs = expr;
    mem->text = ExpectIdentifier(Subclause("12.7.3")).text;
    expr = mem;
  }
  return expr;
}

Stmt* Parser::ParseForeachStmt() {
  auto* stmt = arena_.Create<Stmt>();
  stmt->kind = StmtKind::kForeach;
  stmt->range.start = CurrentLoc();
  Expect(TokenKind::kKwForeach, Subclause("12.7.3"));
  Expect(TokenKind::kLParen, Subclause("12.7.3"));

  stmt->expr = ParseForeachArrayId();
  Expect(TokenKind::kLBracket, Subclause("12.7.3"));
  ParseForeachVars(stmt->foreach_vars);
  Expect(TokenKind::kRBracket, Subclause("12.7.3"));
  Expect(TokenKind::kRParen, Subclause("12.7.3"));
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
  Expect(TokenKind::kKwDo, Subclause("12.7.5"));
  stmt->body = ParseStmt();
  Expect(TokenKind::kKwWhile, Subclause("12.7.5"));
  Expect(TokenKind::kLParen, Subclause("12.7.5"));
  stmt->condition = ParseExpr();
  Expect(TokenKind::kRParen, Subclause("12.7.5"));
  Expect(TokenKind::kSemicolon, Subclause("12.7.5"));
  return stmt;
}

}  // namespace delta
