// The loop statements of IEEE 1800-2023 §12.7 other than for: while, forever,
// repeat, foreach and do-while. The for statement stays in parser_stmt.cpp
// because it reads its initialisers through ParserStmtHelpers, which is
// file-local to that translation unit. The split keeps both files inside the
// 1000-line limit assert-no-oversized-source-files enforces.

#include <vector>

#include "common/diagnostic.h"
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

// A.6.8 writes the foreach array as a ps_or_hierarchical_array_identifier,
// which A.9.3 spells `[ implicit_class_handle . | class_scope | package_scope
// ] hierarchical_array_identifier`: a name reached through `this.` or
// `super.`, a class or package scope's `::`, or a hierarchical path's '.'.
// Read as the member-access chain an expression's name is, which is the
// shape the elaborator's and simulator's name walks take; the parser had
// built a chain of its own shape that took '.' alone, so `pkg::arr`,
// `this.arr` and `C::arr` were reported as a missing identifier or '['.
//
// A.9.3's hierarchical_identifier is `{ identifier constant_bit_select . }
// identifier` (printed page 1214 of IEEE 1800-2023), so a segment before
// a '.' may select an element: in `foreach
// (successors[s].m_predecessors[pred])` the array is the member of the selected
// element and `[pred]` alone is the loop_variables §12.7.3 puts after the array
// (printed page 331). A run of bracket groups is a select when a '.' follows it
// and the loop_variables when the `)` does; the parser had taken the first
// group for the loop variables and asked for `)` at the '.'.
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
    while (Check(TokenKind::kLBracket)) result = ParseSelectExpr(result);
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
  // A.6.8 ends foreach with a statement, where the five other loops end with
  // a statement_or_null: a ';' here is no body.
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
