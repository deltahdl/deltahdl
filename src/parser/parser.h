#pragma once

#include <unordered_set>

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
  // Module/package parsing
  ModuleDecl* ParseModuleDecl();
  PackageDecl* ParsePackageDecl();
  ModuleItem* ParseImportDecl();
  void ParsePortList(ModuleDecl& mod);
  PortDecl ParsePortDecl();
  void ParseModuleBody(ModuleDecl& mod);
  void ParseModuleItem(std::vector<ModuleItem*>& items);
  bool TryParseKeywordItem(std::vector<ModuleItem*>& items);
  void ParseParamPortDecl(ModuleDecl& mod);
  void ParseParamsPortsAndSemicolon(ModuleDecl& decl);

  // Generate blocks (parser_generate.cpp)
  void ParseGenerateRegion(std::vector<ModuleItem*>& items);
  ModuleItem* ParseGenerateFor();
  ModuleItem* ParseGenerateIf();
  ModuleItem* ParseGenerateCase();

  // Top-level declarations (parser_toplevel.cpp)
  ModuleDecl* ParseInterfaceDecl();
  ModuleDecl* ParseProgramDecl();
  ModportDecl* ParseModportDecl();
  ClassDecl* ParseClassDecl();
  ClassMember* ParseClassMember();
  ClassMember* ParseConstraintStub(ClassMember* member);

  // Gate primitives (parser_toplevel.cpp)
  bool IsAtGateKeyword();
  ModuleItem* ParseGateInst();

  // Declarations (parser_decl.cpp)
  ModuleItem* ParseDefparam();
  ModuleItem* ParseTypedef();
  DataType ParseEnumType();
  DataType ParseStructOrUnionType();
  ModuleItem* ParseFunctionDecl();
  ModuleItem* ParseTaskDecl();
  std::vector<FunctionArg> ParseFunctionArgs();

  // Declarations
  void ParseVarDeclList(std::vector<ModuleItem*>& items, const DataType& dtype);
  ModuleItem* ParseContinuousAssign();
  ModuleItem* ParseParamDecl();
  ModuleItem* ParseAlwaysBlock(AlwaysKind kind);
  ModuleItem* ParseInitialBlock();
  ModuleItem* ParseFinalBlock();
  void ParseTypedItemOrInst(std::vector<ModuleItem*>& items);
  void ParseImplicitTypeOrInst(std::vector<ModuleItem*>& items);
  ModuleItem* ParseModuleInst(const Token& module_tok);
  void ParsePortConnection(ModuleItem* item);
  void ParseParenList(std::vector<Expr*>& out);

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
  Stmt* ParseDoWhileStmt();
  Stmt* ParseSimpleKeywordStmt(StmtKind kind);
  Stmt* ParseReturnStmt();
  Stmt* ParseWaitStmt();
  Stmt* ParseDisableStmt();
  Stmt* ParseAssignmentOrExprStmt();
  Stmt* ParseAssignmentOrExprNoSemi();
  Stmt* ParseDelayStmt();
  Stmt* ParseEventControlStmt();

  // Expressions (Pratt parser — in expr_parser.cpp)
  Expr* ParseExpr();
  Expr* ParseExprBp(int min_bp);
  Expr* ParseInfixBp(Expr* lhs, int min_bp);
  Expr* ParsePrefixExpr();
  Expr* ParsePrimaryExpr();
  Expr* MakeLiteral(ExprKind kind, const Token& tok);
  Expr* ParseCallExpr(Expr* callee);
  Expr* ParseIdentifierExpr();
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
  std::unordered_set<std::string_view> known_types_;
};

}  // namespace delta
