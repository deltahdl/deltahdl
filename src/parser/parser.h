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
  void ParseTopLevel(CompilationUnit* unit);

  // Module/package parsing
  ModuleDecl* ParseModuleDecl();
  ModuleDecl* ParseExternModuleDecl();
  PackageDecl* ParsePackageDecl();
  void ParseImportDecl(std::vector<ModuleItem*>& items);
  ModuleItem* ParseImportItem();
  void ParseExportDecl(std::vector<ModuleItem*>& items);
  void ParsePortList(ModuleDecl& mod);
  void ParseNonAnsiPortList(ModuleDecl& mod);
  PortDecl ParsePortDecl();
  void ParseModuleBody(ModuleDecl& mod);
  void ParseNonAnsiPortDecls(ModuleDecl& mod);
  void ParseModuleItem(std::vector<ModuleItem*>& items);
  bool TryParseKeywordItem(std::vector<ModuleItem*>& items);
  bool TryParseVerificationItem(std::vector<ModuleItem*>& items);
  void ParseGenvarDecl(std::vector<ModuleItem*>& items);
  void ParseTimeunitDecl();
  bool TryParseClockingOrVerification(std::vector<ModuleItem*>& items);
  void ParseParamPortDecl(ModuleDecl& mod);
  void ParseParamsPortsAndSemicolon(ModuleDecl& decl);

  // Generate blocks (parser_generate.cpp)
  void ParseGenerateRegion(std::vector<ModuleItem*>& items);
  void ParseGenerateBody(std::vector<ModuleItem*>& body);
  ModuleItem* ParseGenerateFor();
  ModuleItem* ParseGenerateIf();
  ModuleItem* ParseGenerateCase();

  // Top-level declarations (parser_toplevel.cpp)
  ModuleDecl* ParseInterfaceDecl();
  ModuleDecl* ParseProgramDecl();
  void ParseModportDecl(std::vector<ModportDecl*>& out);
  ModportPort ParseModportPort(Direction& cur_dir);
  ClassDecl* ParseClassDecl();
  ClassMember* ParseClassMember();
  ClassMember* ParseConstraintStub(ClassMember* member);

  // Gate primitives (parser_toplevel.cpp)
  bool IsAtGateKeyword();
  void ParseGateInst(std::vector<ModuleItem*>& items);
  ModuleItem* ParseOneGateInstance(GateKind kind, SourceLoc loc);
  uint8_t ParseStrength0();
  uint8_t ParseStrength1();
  Expr* ParseGateDelay();

  // User-defined primitives (parser_toplevel.cpp)
  UdpDecl* ParseUdpDecl();

  // Verification constructs (parser_verify.cpp — §17/§18/§19)
  ModuleDecl* ParseCheckerDecl();
  Stmt* ParseRandcaseStmt();
  void ParseCovergroupDecl(std::vector<ModuleItem*>& items);
  void SkipCovergroupItem();

  // Declarations (parser_decl.cpp)
  ModuleItem* ParseDefparam();
  ModuleItem* ParseTypedef();
  ModuleItem* ParseNettypeDecl();
  DataType ParseEnumType();
  DataType ParseEnumBody(const DataType& base);
  DataType ParseStructOrUnionType();
  DataType ParseStructOrUnionBody(TokenKind kw);
  ModuleItem* ParseFunctionDecl();
  ModuleItem* ParseTaskDecl();
  std::vector<FunctionArg> ParseFunctionArgs();
  void ParseOldStylePortDecls(ModuleItem* item, TokenKind end_kw);

  // Declarations
  void ParseVarDeclList(std::vector<ModuleItem*>& items, const DataType& dtype);
  ModuleItem* ParseContinuousAssign();
  ModuleItem* ParseAlias();
  ModuleItem* ParseParamDecl();
  ModuleItem* ParseAlwaysBlock(AlwaysKind kind);
  ModuleItem* ParseInitialBlock();
  ModuleItem* ParseFinalBlock();
  void ParseTypedItemOrInst(std::vector<ModuleItem*>& items);
  void ParseImplicitTypeOrInst(std::vector<ModuleItem*>& items);
  ModuleItem* ParseModuleInst(const Token& module_tok);
  void ParsePortConnection(ModuleItem* item);
  void ParseUnpackedDims(std::vector<Expr*>& dims);
  void ParseParenList(std::vector<Expr*>& out);

  // Statements (parser_stmt.cpp)
  Stmt* ParseStmt();
  Stmt* ParseStmtBody();
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
  Stmt* ParseForeachStmt();
  Expr* ParseForeachArrayId();
  void ParseForeachVars(std::vector<std::string_view>& vars);
  Stmt* ParseSimpleKeywordStmt(StmtKind kind);
  Stmt* ParseReturnStmt();
  Stmt* ParseWaitStmt();
  Stmt* ParseDisableStmt();
  Stmt* ParseEventTriggerStmt();
  Stmt* ParseAssignmentOrExprStmt();
  Stmt* ParseAssignmentOrExprNoSemi();
  Stmt* ParseDelayStmt();
  Stmt* ParseEventControlStmt();
  void ParseIntraAssignTiming(Stmt* stmt);
  Stmt* ParseProceduralAssignStmt();
  Stmt* ParseProceduralDeassignStmt();
  Stmt* ParseForceStmt();
  Stmt* ParseReleaseStmt();

  // Clocking blocks and interprocess sync (parser_clocking.cpp — §14, §15)
  ModuleItem* ParseClockingDecl();
  void ParseClockingItem(ModuleItem* item);
  void ParseClockingSkew(Edge& edge, Expr*& delay);
  Stmt* ParseWaitOrderStmt();

  // Assertions (parser_assert.cpp — §16)
  Stmt* ParseImmediateAssert();
  Stmt* ParseImmediateAssume();
  Stmt* ParseImmediateCover();
  ModuleItem* ParseAssertProperty();
  ModuleItem* ParseAssumeProperty();
  ModuleItem* ParseCoverProperty();
  ModuleItem* ParsePropertyDecl();
  ModuleItem* ParseSequenceDecl();

  // Expressions (Pratt parser — in expr_parser.cpp)
  Expr* ParseExpr();
  Expr* ParseExprBp(int min_bp);
  Expr* ParseInfixBp(Expr* lhs, int min_bp);
  Expr* ParsePrefixExpr();
  Expr* ParsePrimaryExpr();
  Expr* MakeLiteral(ExprKind kind, const Token& tok);
  Expr* ParseCallExpr(Expr* callee);
  void ParseNamedArg(Expr* call);
  Expr* ParseIdentifierExpr();
  Expr* ParseSelectExpr(Expr* base);
  Expr* ParseSystemCall();
  Expr* ParseConcatenation();
  Expr* ParseAssignmentPattern();
  Expr* ParseCastExpr();
  Expr* ParseTypeRefExpr();
  Expr* ParseWithClause(Expr* expr);
  Expr* ParseParenExpr();
  Expr* ParseCompoundAssignExpr(Expr* lhs);
  Expr* ParseInsideExpr(Expr* lhs);
  void ParseInsideRangeList(std::vector<Expr*>& out);
  Expr* ParseInsideValueRange();
  Expr* ParseStreamingConcat(TokenKind dir);
  Expr* ParseMinTypMaxExpr();

  // Attributes (§5.12)
  std::vector<Attribute> ParseAttributes();
  static void AttachAttrs(std::vector<ModuleItem*>& items, size_t before,
                          const std::vector<Attribute>& attrs);

  // Types
  DataType ParseDataType();

  // Event lists
  std::vector<EventExpr> ParseEventList();
  EventExpr ParseSingleEvent();

  // Utilities
  Token Expect(TokenKind kind);
  Token ExpectIdentifier();
  bool CheckIdentifier();
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
