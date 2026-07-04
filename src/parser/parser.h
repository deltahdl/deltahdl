#pragma once

#include <functional>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "lexer/lexer.h"
#include "parser/ast.h"

namespace delta {

class Parser {
 public:
  Parser(Lexer& lexer, Arena& arena, DiagEngine& diag);

  CompilationUnit* Parse();
  CompilationUnit* ParseLibraryText();

 private:
  // Shared gate/UDP instance-tail parser (see parser_instance_internal.h).
  friend void ParseGateInstanceTail(Parser& p, ModuleItem* item, bool has_name);
  // File-local CPD-dedup helpers (defined static in their respective TUs).
  friend struct ParserStmtHelpers;
  friend struct ParserPortHelpers;

  void ParseTopLevel(CompilationUnit* unit);
  bool TryParsePrimaryTopLevel(CompilationUnit* unit);
  bool TryParseAnonymousProgram(CompilationUnit* unit);
  void ParseExternTopLevel(CompilationUnit* unit);
  bool TryParseSecondaryTopLevel(CompilationUnit* unit);
  bool TryParseCuScopeDataDecl(CompilationUnit* unit);
  bool TryParseCuScopeItem(CompilationUnit* unit);
  void ParseOutOfBlockConstraint(CompilationUnit* unit);

  ModuleDecl* ParseModuleDecl();
  ModuleDecl* ParseExternModuleDecl();
  PackageDecl* ParsePackageDecl();
  bool TryParsePackageBodyItem(std::vector<ModuleItem*>& items);
  void ParseImportDecl(std::vector<ModuleItem*>& items);
  ModuleItem* ParseImportItem();
  void ParseExportDecl(std::vector<ModuleItem*>& items);
  ModuleItem* ParseDpiImport();
  ModuleItem* ParseDpiExport(SourceLoc loc);
  void ParsePortList(ModuleDecl& mod);
  void ParseNonAnsiPortList(ModuleDecl& mod);
  PortDecl ParsePortDecl();
  void ParseModuleBody(ModuleDecl& mod);
  void ParseNonAnsiPortDecls(ModuleDecl& mod);
  void ParseModuleItem(std::vector<ModuleItem*>& items);
  std::string_view TryParseAssertionItemLabel();
  void ParseDataDeclItem(std::vector<ModuleItem*>& items, size_t before,
                         const std::vector<Attribute>& attrs);
  bool TryParseTypeRef(std::vector<ModuleItem*>& items);
  bool TryParseProcessBlock(std::vector<ModuleItem*>& items);
  bool TryParseKeywordItem(std::vector<ModuleItem*>& items);
  bool TryParseDeclKeywordItem(std::vector<ModuleItem*>& items);
  bool TryParseMiscKeywordItem(std::vector<ModuleItem*>& items);
  bool TryParseNonPortItem(std::vector<ModuleItem*>& items);
  bool TryParseClassOrVerification(std::vector<ModuleItem*>& items);
  bool TryParseVerificationItem(std::vector<ModuleItem*>& items);
  ModuleItem* ParseLetDecl();
  FunctionArg ParseLetArg();
  void ParseGenvarDecl(std::vector<ModuleItem*>& items);
  void ParseTimeunitDecl(ModuleDecl* mod = nullptr,
                         CompilationUnit* cu = nullptr,
                         PackageDecl* pkg = nullptr);
  bool TryParseClockingOrVerification(std::vector<ModuleItem*>& items);
  void ParseParamPortDecl(
      std::vector<std::pair<std::string_view, Expr*>>& params,
      std::unordered_set<std::string_view>& type_param_names,
      std::unordered_set<std::string_view>& localparam_port_names,
      bool& is_localparam_group, std::vector<DataType>* param_types = nullptr);
  void ParseParamsPortsAndSemicolon(ModuleDecl& decl);

  void ParseGenerateRegion(std::vector<ModuleItem*>& items);
  void ParseGenerateBody(std::vector<ModuleItem*>& body,
                         std::string_view& out_label);
  ModuleItem* ParseGenerateFor();
  ModuleItem* ParseGenerateIf();
  void ParseGenerateCaseLabel(GenerateCaseItem& ci);
  ModuleItem* ParseGenerateCase();

  ModuleDecl* ParseInterfaceDecl();
  ModuleDecl* ParseProgramDecl();
  void ParseModportDecl(std::vector<ModportDecl*>& out);
  void ParseModportItem(ModportDecl* mp);
  void ParseModportPortEntry(ModportDecl* mp, Direction& cur_dir, int& tf_mode);
  ModportPort ParseModportTfPort(bool is_import);
  ModportPort ParseModportSimplePort(Direction dir);
  bool IsAtClassDecl();
  ClassDecl* ParseClassDecl();
  void ParseClassExtendsClause(ClassDecl* decl, bool is_implements);
  void ParseExtendsArgList(ClassDecl* decl);
  void ValidateConstructorQualifiers(ClassMember* member);
  void ParseClassMembers(std::vector<ClassMember*>& members);
  bool TryParseMethodOrConstraint(std::vector<ClassMember*>& members,
                                  ClassMember* member, bool proto);
  bool TryParseKeywordClassMember(std::vector<ClassMember*>& members,
                                  ClassMember* member, bool proto);
  bool ParseClassQualifiers(ClassMember* member);
  bool VirtualIsClassQualifier();
  bool TryConsumeClassQualifier(ClassMember* m, TokenKind kw,
                                bool ClassMember::* flag, const char* dup_msg);
  bool TryConsumeAccessQualifier(ClassMember* m);
  bool TryConsumeVirtualQualifier(ClassMember* m);
  bool TryConsumeRandQualifier(ClassMember* m);
  void ValidateClassMethod(ClassMember* member);
  void ParseExtraPropertyDecls(std::vector<ClassMember*>& members,
                               const ClassMember* first, const DataType& dtype);
  ClassMember* ParseConstraintStub(ClassMember* member);
  bool ParseConstraintHeader(ClassMember* member);
  bool ScanConstraintBodyToken(ClassMember* member, int& depth, bool& in_soft,
                               bool carried_qualifier);
  void CaptureConstraintRelation(ClassMember* member);
  void CaptureLinearSequenceBody(ModuleItem* item);
  bool ParseLinearSeqOperands(std::vector<Expr*>& operands);
  void CheckConstraintExprToken(const Token& tok);
  void CheckForeachConstraintHeader(ClassMember* member);
  void CheckSolveBeforeConstraint(ClassMember* member);
  void ParseSolveBeforeList(std::vector<ConstraintSolveBeforeEntry>& out);
  void CheckDistSet();

  bool IsAtGateKeyword();
  void ParseGateInst(std::vector<ModuleItem*>& items);
  void ParseInlineGateTerminals(GateKind kind, SourceLoc loc,
                                std::vector<ModuleItem*>& items);
  ModuleItem* ParseOneGateInstance(GateKind kind, SourceLoc loc);
  uint8_t ParseStrength0();
  uint8_t ParseStrength1();
  void ParseGateDelay(Expr*& d1, Expr*& d2, Expr*& d3);

  UdpDecl* ParseUdpDecl();
  void ParseUdpAnsiOutputHeader(UdpDecl* udp);
  void ParseUdpNonAnsiHeader(UdpDecl* udp);
  void ParseUdpInitialStatement(UdpDecl* udp);
  UdpDecl* ParseExternUdpDecl();
  char ParseUdpInitialValue(TokenKind stop1, TokenKind stop2);
  void ParseUdpOutputDecl(UdpDecl* udp);
  void ParseUdpPortDecls(UdpDecl* udp);
  void ParseUdpTable(UdpDecl* udp);
  void ParseUdpTableRow(UdpDecl* udp);

  void RejectUdpPortDimension();

  void RejectUdpInoutPort();

  void ValidateUdpHeader(UdpDecl* udp);

  void ValidateUdpTable(UdpDecl* udp);
  bool TryParseStrengthSpec(uint8_t& str0, uint8_t& str1);
  ModuleItem* ParseOneUdpInstance(const Token& udp_tok, SourceLoc loc);
  void ParseUdpInstList(const Token& udp_tok, std::vector<ModuleItem*>& items);

  ModuleDecl* ParseCheckerDecl();
  Stmt* ParseRandcaseStmt();
  Stmt* ParseRandsequenceStmt();
  RsProduction ParseRsProduction();
  RsRule ParseRsRule();
  void ParseRsRuleRandJoin(RsRule& rule);
  void ParseRsRuleWeight(RsRule& rule);
  RsProd ParseRsProd();
  void ParseRsProdIf(RsProd& prod);
  void ParseRsProdRepeat(RsProd& prod);
  void ParseRsProdCase(RsProd& prod);
  void ParseRsCodeBlockStmts(std::vector<Stmt*>& stmts);
  bool CheckColonEq();
  bool MatchColonEq();
  bool CheckColonSlash();
  bool MatchColonSlash();
  RsProductionItem ParseRsProductionItem();
  RsCaseItem ParseRsCaseItem();
  void ParseCovergroupDecl(std::vector<ModuleItem*>& items);
  // Scan state shared by the tf_port-style formal-list scanners
  // (ParseCovergroupFormalList / ParseSampleFormalList). A single
  // classification step is performed by StepTfPortFormalScan.
  struct TfPortFormalScan {
    int depth = 1;
    std::string_view pending;
    SourceLoc pending_loc;
    bool have_pending = false;
    bool in_default = false;
  };
  void StepTfPortFormalScan(TfPortFormalScan& st,
                            const std::function<void()>& flush,
                            const std::function<bool()>& reject_direction);
  void ParseCovergroupFormalList(std::vector<std::string>& names);
  void ParseSampleFormalList(
      const std::vector<std::string>& covergroup_formals);
  void ParseBlockEventExpression();
  void SkipCovergroupItem();

  ModuleItem* ParseSpecifyBlock();
  void ParseSpecparamDecl(std::vector<ModuleItem*>& items);
  void ParseSpecifyItem(std::vector<SpecifyItem*>& items);
  SpecifyItem* ParseSpecifyPathDecl();
  SpecifyItem* ParseConditionalPathDecl(Expr* cond);
  SpecifyItem* ParseIfnonePathDecl();
  SpecifyItem* ParseTimingCheck();
  SpecifyItem* ParsePulsestyleDecl();
  SpecifyItem* ParseShowcancelledDecl();
  void ParseSpecparamInSpecify(std::vector<SpecifyItem*>& items);
  void ParsePathPorts(std::vector<SpecifyTerminal>& ports);
  SpecifyTerminal ParseSpecifyTerminal();
  void ParsePathDelays(std::vector<Expr*>& delays);
  SpecifyEdge ParseSpecifyEdge(
      std::vector<std::pair<char, char>>* edge_descriptors = nullptr);
  void ParseEdgeDescriptorList(std::vector<std::pair<char, char>>& descriptors);
  SpecifyPolarity ParseSpecifyPolarity();
  TimingCheckKind ParseTimingCheckKind(std::string_view name);
  static bool IsTimingCheckName(std::string_view name);
  bool CheckNextIsCommaOrRParen();
  void ParseTimingCheckTrailingArgs(TimingCheckDecl& tc);
  void ParseExtendedTimingCheckArgs(TimingCheckDecl& tc);
  void ParseTimeskewExtendedArgs(TimingCheckDecl& tc);
  void ParseSetupholdExtendedArgs(TimingCheckDecl& tc);
  void ParseOptionalDelayedRef(std::string_view& name, Expr*& expr);

  LibraryDecl* ParseLibraryDecl();
  IncludeStmt* ParseLibraryIncludeStmt();
  std::string_view ParseFilePathSpec();
  // Copies text into the parser arena so the resulting view outlives the
  // SourceManager that produced the token (needed for library-map loading,
  // which parses each map file with a throwaway local SourceManager).
  std::string_view ArenaCopy(std::string_view text);

  BindDirective* ParseBindDirective();

  ConfigDecl* ParseConfigDecl();
  void ParseDesignStatement(ConfigDecl* decl);
  ConfigRule* ParseConfigRule();
  void ParseLiblistClause(ConfigRule* rule);
  void ParseUseClause(ConfigRule* rule);
  void ParseNamedParamAssignment(ConfigRule* rule);

  ModuleItem* ParseDefparam();
  ModuleItem* ParseTypedef();
  bool TryForwardClassTypedef(ModuleItem* item);
  bool TryForwardAggregateTypedef(ModuleItem* item);
  bool TryForwardBareTypedef(ModuleItem* item);
  void SkipBracketedDims();
  void SkipBalancedParens();
  bool TryInterfacePortTypedef(ModuleItem* item);
  ModuleItem* ParseNettypeDecl();
  DataType ParseEnumType();
  DataType ParseEnumBody(const DataType& base);
  DataType ParseStructOrUnionType();
  DataType ParseStructOrUnionBody(TokenKind kw);
  void ParseStructMembers(DataType& dtype);
  DataType ParseStructMemberType();
  void ParseStructMemberList(DataType& dtype, const DataType& member_type,
                             const std::vector<Attribute>& member_attrs,
                             bool is_rand, bool is_randc);
  DataType ParseFunctionReturnType();
  // Dispatches an inline enum/struct/union type (which ParseDataType does not
  // handle) into the appropriate parser, applying any trailing packed dims.
  // Returns true and fills dt when an aggregate keyword was consumed.
  bool TryParseInlineAggregateType(DataType& dt);
  void ParseDynamicOverrideSpecifiers(ModuleItem* item);
  void ParseOneOverrideSpecifier(ModuleItem* item);
  Direction ParseArgDirection(FunctionArg& arg, Direction sticky_dir,
                              bool* was_explicit = nullptr);
  void ParseFuncName(ModuleItem* item);
  void ParseFuncBody(ModuleItem* item);
  ModuleItem* ParseFunctionDecl(bool prototype_only = false);
  ModuleItem* ParseTaskDecl(bool prototype_only = false);
  // Carried state of the tf_port_item scan in ParseFunctionArgs (§8.17/§13.3):
  // sticky direction, whether a 'default' sentinel was seen, the previous
  // argument's data type, whether this is the first argument, and whether the
  // previous slot was the 'default' sentinel.
  struct FuncArgScan {
    Direction sticky_dir = Direction::kInput;
    bool seen_default = false;
    DataType prev_data_type;
    bool first_arg = true;
    bool prev_was_default = false;
  };
  std::vector<FunctionArg> ParseFunctionArgs(bool require_identifiers = true);
  bool TryParseDefaultArgSentinel(std::vector<FunctionArg>& args,
                                  FuncArgScan& scan);
  void ParseFunctionArgTrailer(FunctionArg& arg, bool require_identifiers);
  void ParseOneFunctionArg(std::vector<FunctionArg>& args, FuncArgScan& scan,
                           bool require_identifiers);
  // Shared header of one tf_port_declaration (direction/const/static + type)
  // whose declarator list is parsed by ParseTfPortDeclarators.
  struct TfPortHeader {
    Direction dir = Direction::kInput;
    bool is_const = false;
    bool is_ref_static = false;
    DataType dt;
  };
  void ParseOldStylePortDecls(ModuleItem* item, TokenKind end_kw);
  Direction ParseTfPortDirection();
  void ParseTfPortDeclarators(ModuleItem* item, const TfPortHeader& hdr);

  uint8_t ParseChargeStrength();
  void ParseDriveStrength(uint8_t& s0, uint8_t& s1);
  void ParseNetStrength(DataType& dtype);
  void ParseVarDeclList(std::vector<ModuleItem*>& items, const DataType& dtype);
  void ParseContinuousAssign(std::vector<ModuleItem*>& items);
  ModuleItem* ParseAlias();
  void ParseParamDecl(std::vector<ModuleItem*>& items);
  void ParseImplicitParamRange(DataType& dtype);
  void ParseTypeParamDecl(std::vector<ModuleItem*>& items, SourceLoc loc,
                          bool localparam = false);
  ModuleItem* ParseAlwaysBlock(AlwaysKind kind);
  ModuleItem* ParseInitialBlock();
  ModuleItem* ParseFinalBlock();
  void ParseVarPrefixed(std::vector<ModuleItem*>& items);
  void ParseTypedItemOrInst(std::vector<ModuleItem*>& items,
                            bool had_lifetime = false);
  void ParseImplicitTypeOrInst(std::vector<ModuleItem*>& items);
  void RejectInstInProgram(SourceLoc loc, const char* msg);
  void ParseScopedTypeOrInst(const Token& name_tok,
                             std::vector<ModuleItem*>& items);
  bool LooksLikeScopedInstTail();
  void ParsePlainVarDecl(const Token& name_tok,
                         std::vector<ModuleItem*>& items);
  ModuleItem* ParseModuleInst(const Token& module_tok);
  ModuleItem* ParseModuleInstList(const Token& module_tok,
                                  std::vector<ModuleItem*>* extra_items);
  void ParseParamValueAssignment(
      std::vector<std::pair<std::string_view, Expr*>>& out);
  bool ParseParamValueEntry(
      std::vector<std::pair<std::string_view, Expr*>>& out);
  bool ParsePortConnection(ModuleItem* item);
  void ParseUnpackedDims(std::vector<Expr*>& dims);
  void ParseParenList(std::vector<Expr*>& out);
  std::vector<DataType> ParseTypeParamList();
  DataType ParseOneTypeParam();
  DataType ParseNamedType();

  Stmt* ParseStmt();
  std::string_view TryParseStmtLabel();
  Stmt* ParseStmtBody(std::string_view prefix_label = {});
  Stmt* ParseBlockStmt(std::string_view prefix_label = {});
  Stmt* ParseIfStmt();
  Stmt* ParseCaseStmt(TokenKind case_kind);
  CaseItem ParseCaseItem(bool inside = false);
  Stmt* ParseForStmt();
  Stmt* ParseWhileStmt();
  Stmt* ParseForeverStmt();
  Stmt* ParseRepeatStmt();
  Stmt* ParseForkStmt(std::string_view prefix_label = {});
  Stmt* ParseDoWhileStmt();
  Stmt* ParseForeachStmt();
  Expr* ParseForeachArrayId();
  void ParseForeachVars(std::vector<std::string_view>& vars);
  Stmt* ParseSimpleKeywordStmt(StmtKind kind);
  Stmt* ParseReturnStmt();
  Stmt* ParseWaitStmt();
  Stmt* ParseDisableStmt();
  Stmt* ParseEventTriggerStmt();
  Stmt* ParseNbEventTriggerStmt();
  Stmt* ParseAssignmentOrExprStmt();
  Stmt* ParseAssignmentOrExprNoSemi();
  Stmt* ParseCycleDelayStmt();
  Stmt* ParseDelayStmt();
  Stmt* ParseEventControlStmt();
  void ParseIntraAssignTiming(Stmt* stmt);
  Stmt* ParseProceduralAssignStmt();
  Stmt* ParseProceduralDeassignStmt();
  Stmt* ParseForceStmt();
  Stmt* ParseReleaseStmt();
  bool IsBlockVarDeclStart();
  bool IsBlockVarDeclStartCore();
  // True when a leading known-type name is actually a scoped statement
  // (Class::method(...) call or Class::prop = ... assignment), not a
  // scoped-type declaration. Assumes the current token is the type name.
  bool IsScopedCallOrAssignStmt();
  void ParseBlockVarDecls(std::vector<Stmt*>& stmts);
  void ParseBlockDataDecl(std::vector<Stmt*>& stmts,
                          const std::vector<Attribute>& attrs);

  ModuleItem* ParseClockingDecl();
  void ParseClockingItemList(ModuleItem* item);
  void ParseClockingItem(ModuleItem* item);
  void ParseClockingSkew(Edge& edge, Expr*& delay);
  Direction ParseClockingDirection(Edge& in_edge, Expr*& in_delay,
                                   Edge& out_edge, Expr*& out_delay);
  Stmt* ParseWaitOrderStmt();

  Stmt* ParseImmediateAssert();
  Stmt* ParseImmediateAssume();
  Stmt* ParseImmediateAssertLike(StmtKind kind, TokenKind keyword);

  Stmt* ParseProceduralConcurrentAssertLike(StmtKind kind);
  ModuleItem* ParseDeferredImmediateItem(SourceLoc loc, StmtKind kind);
  Stmt* ParseExpectStmt();
  Stmt* ParseImmediateCover();
  ModuleItem* ParseAssertProperty();
  ModuleItem* ParseAssumeProperty();
  ModuleItem* ParsePropertyAssertLike(ModuleItemKind kind, TokenKind keyword);
  bool TryParseSimpleConcurrentProperty(ModuleItem* item);
  bool BodyHasTemporalOperator();
  ModuleItem* ParseCoverProperty();
  ModuleItem* ParseRestrictProperty();
  ModuleItem* ParsePropertyDecl();
  ModuleItem* ParseSequenceDecl();
  void ValidateLiteralCycleDelayRange(SourceLoc range_loc);
  void HarvestAssertionVariableDecl(ModuleItem* item);

  Expr* ParseExpr();
  Expr* ParseExprBp(int min_bp);
  Expr* ParseInfixBp(Expr* lhs, int min_bp);
  Expr* TryParseSpecialInfix(Expr*& lhs, const Token& tok, int min_bp);
  Expr* ParsePrefixExpr();
  Expr* ParsePrimaryExpr();
  Expr* ParseIntLiteralPrimary(const Token& tok);
  Expr* ParseTypeRefPrimary();
  Expr* ParseThisOrSuperExpr();
  Expr* ParseCastOrTypedPattern();
  Expr* MakeLiteral(ExprKind kind, const Token& tok);
  void WarnSizedOverflow(const Token& tok);
  Expr* ParseCallExpr(Expr* callee);
  void CheckRandomizeArgList(const Expr* call);
  void ParseCallArgs(Expr* call);
  void ParseNamedArg(Expr* call);
  void ParseTrailingNamedArgs(Expr* call);
  Expr* ParseMemberAccessChain(Token tok);
  Expr* MakeMemberAccess(Expr* base);
  void ParseParamValueAssignment(Expr* base);
  Expr* ParseParameterizedScope(Expr* base);
  Expr* TryParseUserTypeCast(const Token& tok);
  Expr* ParseIdentifierExpr();
  Expr* ParseLocalScopeExpr();
  Expr* TryParseIdentifierCast(Expr* base, bool* handled);
  Expr* ParseIdentifierPostfixChain(Expr* result);
  Expr* ParseWithClauseTail(Expr* result);
  Expr* ParseSelectExpr(Expr* base);
  Expr* ParseSystemCall();
  Expr* MakeSysScopePrefix(const Token& sys_tok);
  Expr* ParseSysRootTail(Expr* expr);
  void ParseSysClockingEventArg(Expr* call);
  void ParseSysCallArgs(Expr* call);
  Expr* ParseConcatenation();
  Expr* ParseAssignmentPattern();
  Expr* ParsePatternReplication(Expr* count, SourceLoc loc);
  bool ParseFirstPatternElement(Expr* pat, bool& named);
  Expr* ParseCastExpr();
  Expr* ParseTypeRefExpr();
  Expr* ParseWithClause(Expr* expr);
  Expr* ParseParenExpr();
  Expr* ParseCompoundAssignExpr(Expr* lhs);
  Expr* ParseInsideExpr(Expr* lhs);
  void ParseInsideRangeList(std::vector<Expr*>& out);
  Expr* ParseInsideValueRange();
  Expr* ParseNewExpr();
  Expr* ParseTaggedExpr();
  Expr* ParseStreamingConcat(TokenKind dir);
  Expr* ParseMinTypMaxExpr();

  std::vector<Attribute> ParseAttributes();
  static void AttachAttrs(std::vector<ModuleItem*>& items, size_t before,
                          const std::vector<Attribute>& attrs);

  DataType ParseDataType();
  bool TryParseNetDataType(DataType& dtype, bool has_intervening);
  void ParsePackedDims(DataType& dtype);
  DataType ParseVirtualInterfaceType();

  std::vector<EventExpr> ParseEventList();
  EventExpr ParseSingleEvent();

  std::string_view ParseDottedPath();
  Token Expect(TokenKind kind);
  Token ExpectIdentifier();
  void MatchEndLabel(std::string_view name);
  bool CheckIdentifier();
  bool Match(TokenKind kind);
  Token Consume();
  Token CurrentToken();
  bool Check(TokenKind kind);
  bool AtEnd();
  SourceLoc CurrentLoc();
  void Synchronize();
  // Synchronize() that guarantees forward progress: a body parse loop that only
  // terminates on its own end keyword would otherwise spin forever when
  // Synchronize() halts on a foreign block-closing keyword without consuming
  // it.
  void SynchronizeWithProgress();

  Lexer& lexer_;
  Arena& arena_;
  DiagEngine& diag_;
  std::unordered_set<std::string_view> known_types_;
  std::unordered_set<std::string_view> known_nettypes_;
  std::unordered_set<std::string_view> known_udps_;
  ModuleDecl* current_module_ = nullptr;
  PackageDecl* current_package_ = nullptr;
  CompilationUnit* current_compilation_unit_ = nullptr;
  bool InProgramBlock() const {
    return current_module_ &&
           current_module_->decl_kind == ModuleDeclKind::kProgram;
  }

  int generate_block_depth_ = 0;
  bool InGenerateBlock() const { return generate_block_depth_ > 0; }

  bool in_generate_region_ = false;

  int class_body_depth_ = 0;
  int package_body_depth_ = 0;
  bool in_cu_scope_param_ = false;
  bool in_anonymous_program_ = false;
  bool ForceLocalparam() const {
    return InGenerateBlock() || class_body_depth_ > 0 ||
           package_body_depth_ > 0 || in_cu_scope_param_;
  }
};

inline bool IsPortDirection(TokenKind tk) {
  return tk == TokenKind::kKwInput || tk == TokenKind::kKwOutput ||
         tk == TokenKind::kKwInout || tk == TokenKind::kKwRef;
}

inline void SkipBraceBlock(Lexer& lexer) {
  int depth = 1;
  while (depth > 0 && !lexer.Peek().Is(TokenKind::kEof)) {
    if (lexer.Peek().Is(TokenKind::kLBrace)) ++depth;
    if (lexer.Peek().Is(TokenKind::kRBrace)) --depth;
    if (depth > 0) lexer.Next();
  }
  if (lexer.Peek().Is(TokenKind::kRBrace)) lexer.Next();
}

}  // namespace delta
