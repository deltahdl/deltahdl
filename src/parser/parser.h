#pragma once

#include "common/arena.h"
#include "common/diagnostic.h"
#include "lexer/lexer.h"
#include "parser/ast.h"

namespace delta {

class Parser {
 public:
  Parser(Lexer& lexer, Arena& arena, DiagEngine& diag);

  CompilationUnit* Parse();

 private:
  // Module parsing
  ModuleDecl* ParseModuleDecl();
  void ParsePortList(ModuleDecl& mod);
  PortDecl ParsePortDecl();
  void ParseModuleBody(ModuleDecl& mod);
  ModuleItem* ParseModuleItem();

  // Declarations
  ModuleItem* ParseNetOrVarDecl(const DataType& dtype);
  ModuleItem* ParseContinuousAssign();
  ModuleItem* ParseParamDecl();
  ModuleItem* ParseAlwaysBlock(AlwaysKind kind);
  ModuleItem* ParseInitialBlock();
  ModuleItem* ParseFinalBlock();

  // Statements
  Stmt* ParseStmt();
  Stmt* ParseBlockStmt();
  Stmt* ParseIfStmt();
  Stmt* ParseCaseStmt(TokenKind case_kind);
  CaseItem ParseCaseItem();
  Stmt* ParseForStmt();
  Stmt* ParseWhileStmt();
  Stmt* ParseForeverStmt();
  Stmt* ParseRepeatStmt();
  Stmt* ParseForkStmt();
  Stmt* ParseAssignmentOrExprStmt();
  Stmt* ParseDelayStmt();
  Stmt* ParseEventControlStmt();

  // Expressions (Pratt parser — in expr_parser.cpp)
  Expr* ParseExpr();
  Expr* ParseExprBp(int min_bp);
  Expr* ParsePrefixExpr();
  Expr* ParsePrimaryExpr();
  Expr* MakeLiteral(ExprKind kind, const Token& tok);
  Expr* ParseCallExpr(Expr* callee);
  Expr* ParseSelectExpr(Expr* base);
  Expr* ParseSystemCall();
  Expr* ParseConcatenation();

  // Types
  DataType ParseDataType();

  // Event lists
  std::vector<EventExpr> ParseEventList();
  EventExpr ParseSingleEvent();

  // Utilities
  Token Expect(TokenKind kind);
  bool Match(TokenKind kind);
  Token Consume();
  Token CurrentToken();
  bool Check(TokenKind kind);
  bool AtEnd();
  SourceLoc CurrentLoc();
  void Synchronize();

  Lexer& lexer_;
  Arena& arena_;
  DiagEngine& diag_;
};

}  // namespace delta
