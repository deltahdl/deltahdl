#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
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
  Token head = Check(TokenKind::kKwThis) || Check(TokenKind::kKwSuper)
                   ? Consume()
                   : ExpectIdentifier(Subclause("12.7.3"));
  Expr* result = ParseMemberAccessChain(head);
  auto selects_before_a_member = [this] {
    auto saved = lexer_.SavePos();
    SkipBracketedDims();
    bool before_member = Check(TokenKind::kDot);
    lexer_.RestorePos(saved);
    return before_member;
  };
  while (Check(TokenKind::kLBracket) && selects_before_a_member()) {
    while (Check(TokenKind::kLBracket)) {
      SourceLoc loc = CurrentLoc();
      result = ParseSelectExpr(result);
      if (result->index_end != nullptr) {
        diag_.Error(loc,
                    "a foreach array is a hierarchical identifier, whose "
                    "selects before a period are bit-selects",
                    Subclause("A.6.8"));
      }
    }
    while (Check(TokenKind::kDot)) result = MakeMemberAccess(result);
  }
  return result;
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
  if (Check(TokenKind::kSemicolon)) {
    diag_.Error(CurrentLoc(),
                "a foreach loop's body is a statement; ';' alone is none",
                Subclause("A.6.8"));
  }
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
