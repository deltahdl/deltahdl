#pragma once

#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/scope_type_names.h"

namespace delta {

// One entry of A.5.2's `udp_declaration_port_list`, read out of the source but
// not yet placed on the UdpDecl it belongs to. §29.3.1's rules about a UDP's
// ports are stated over which of the two entry forms was written and where it
// stands, so those are what an entry carries away from the port list.
struct UdpAnsiPortEntry {
  bool is_output = false;
  bool is_inout = false;
  bool declares_reg = false;
  bool declares_initial = false;
  char initial_value = '0';
  std::string_view name;
  SourceLoc loc;
};

class Parser {
 public:
  Parser(Lexer& lexer, Arena& arena, DiagEngine& diag);

  CompilationUnit* Parse();
  CompilationUnit* ParseLibraryText();

  // §3.12.1 case a) has "all files on a given compilation command line make a
  // single compilation unit (in which case the declarations within those files
  // are accessible following normal visibility rules throughout the entire set
  // of files)", and one parser reads one file. These two are how a caller
  // building that single compilation unit out of several files hands the
  // compilation-unit scope from one file's parse to the next: without them a
  // later file reads `byte_t b;` as an instantiation of a module called byte_t,
  // because whether an identifier names a type decides how the declaration
  // after it parses, and `import p::*;` puts nothing back because the parse has
  // never heard of p.
  //
  // Call AdoptCompilationUnitScope before Parse and read CompilationUnitScope
  // after it. What the second answers with is the compilation-unit scope and
  // nothing narrower: every design element's own type names were taken back out
  // by its TypeNameScope at its closing keyword, which is what makes the set
  // safe to carry into a file that never saw that design element. The package
  // and class entries are what §26.3's import declaration and §8.13's extends
  // clause put back, and they are kept past their scope's closing keyword for
  // exactly that reason, so they are carried whole. known_udps_ is the whole
  // compilation-unit scope already, because TypeNameScope below saves and
  // restores known_types_ and known_nettypes_ alone and nothing else narrows
  // it.
  void AdoptCompilationUnitScope(const CompilationUnitScopeNames& names) {
    AdoptTypeNames(names.own);
    package_types_.insert(names.packages.begin(), names.packages.end());
    class_types_.insert(names.classes.begin(), names.classes.end());
  }
  CompilationUnitScopeNames CompilationUnitScope() const {
    return CompilationUnitScopeNames{
        ScopeTypeNames{known_types_, known_nettypes_, known_udps_},
        package_types_, class_types_};
  }

 private:
  // Shared gate/UDP instance-tail parser (see parser_instance_internal.h).
  friend void ParseGateInstanceTail(Parser& p, ModuleItem* item, bool has_name);
  // File-local CPD-dedup helpers (defined static in their respective TUs).
  friend struct ParserStmtHelpers;
  friend struct ParserStmtBlockHelpers;
  friend struct ParserPortHelpers;
  friend struct ParserAssertHelpers;
  friend struct ParserClassHelpers;
  friend struct ParserClassOverrideHelpers;
  // Expect reports through the diagnostic engine and is reached from nowhere
  // but this class, so the only way to ask what it reports is from inside it.
  // Defined in test/src/unit/test_non_lrm_parser_expect.cpp.
  friend struct ParserExpectAccess;

  void ParseTopLevel(CompilationUnit* unit);
  void ReportUnexpectedTopLevelToken();
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
  bool AtMisplacedMethodQualifier();
  void RejectMisplacedMethodQualifier(std::vector<ModuleItem*>& items);
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
  // else_may_follow says whether A.4.2 lets an `else` stand after the
  // generate_block being read, which is true of the first generate_block of an
  // if_generate_construct and of no other position the production admits. It
  // decides whether the item loop stops at an `else` or hands it on as an item.
  // out_has_begin_end is set true when the block read was the `begin`/`end`
  // form of A.4.2's generate_block and false when it was the single
  // generate_item form or the null block `;`, which is the distinction §27.5
  // rests on and which is not recoverable from the items alone.
  void ParseGenerateBody(std::vector<ModuleItem*>& body,
                         std::string_view& out_label, bool& out_has_begin_end,
                         bool else_may_follow);
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
  void RejectPureVirtualMethodBody(const ClassMember* member, bool is_func);
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
  void ScanConstraintBodyRelations(ClassMember* member);
  ClassMember* CaptureInlineConstraintBlock();
  bool ScanConstraintBodyToken(ClassMember* member, int& depth, bool& in_soft,
                               bool carried_qualifier);
  void CaptureConstraintRelation(ClassMember* member);
  void CaptureSoftConstraintRelation(ClassMember* member);
  void CaptureDisableSoftConstraint(ClassMember* member);
  bool TryCaptureBracedImplication(ClassMember* member);
  bool TryCaptureDist(ClassMember* member, bool is_soft = false);
  bool ParseDistItem(ConstraintDistItem& item);
  bool TryCaptureUnique(ClassMember* member);
  bool ParseDistWeight(ConstraintDistItem& item);
  bool TryCaptureIfElseConstraint(ClassMember* member);
  bool CaptureGuardedIf(Expr* guard, std::vector<Expr*>& out);
  bool CaptureGuardedConstraintSet(Expr* guard, std::vector<Expr*>& out);
  bool CaptureGuardedConstraintItem(Expr* guard, std::vector<Expr*>& out);
  Expr* MakeConstraintImplication(Expr* guard, Expr* consequent);
  Expr* MakeConstraintAnd(Expr* lhs, Expr* rhs);
  Expr* MakeConstraintNot(Expr* operand);
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
  // Chooses between A.5.2's two port lists for the header in hand, and is what
  // both ParseUdpDecl and ParseExternUdpDecl choose on.
  bool UdpPortListIsDeclarations();
  UdpAnsiPortEntry ParseUdpAnsiPortEntry();
  void ParseUdpAnsiHeader(UdpDecl* udp);
  void ParseUdpNonAnsiHeader(UdpDecl* udp);
  void ParseUdpInitialStatement(UdpDecl* udp);
  UdpDecl* ParseExternUdpDecl();
  char ParseUdpInitialValue(TokenKind stop1, TokenKind stop2);
  void ParseUdpOutputDecl(UdpDecl* udp);
  void ParseUdpPortDecls(UdpDecl* udp);
  void ParseUdpTable(UdpDecl* udp);
  // `reg_mismatch_reported` carries §29.3.2's report across the rows of one
  // table, so a table whose every row disagrees with the reg declaration draws
  // one report rather than one per row. ParseUdpTable owns it.
  void ParseUdpTableRow(UdpDecl* udp, bool& reg_mismatch_reported);

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
  void RejectDerivedCovergroupTail();
  void RejectNamedCovergroupExtends();
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
  void ParseSampleFormalList(const std::vector<std::string>& covergroup_formals,
                             std::vector<std::string>& sample_names);
  void ParseBlockEventExpression();
  // §19.7: skip one covergroup-body item. `seen_options` accumulates the
  // covergroup-level coverage options already assigned in this definition so a
  // repeated assignment of the same option can be flagged as an error.
  void SkipCovergroupOptionAssignment(
      const std::vector<std::string>& sample_formals,
      std::unordered_set<std::string>& seen_options);
  void SkipUnlabelledCoverpointItem();
  void SkipLabelledCoverpointItem();
  void SkipCovergroupItem(const std::vector<std::string>& sample_formals,
                          std::unordered_set<std::string>& seen_options);
  // §19.6: consume a cross's list_of_cross_items (positioned just after the
  // `cross` keyword) up to the optional `iff`/body, enforcing that it names at
  // least two bare cover_point/variable identifiers and no direct expressions.
  void ValidateCrossItemList();

  ModuleItem* ParseSpecifyBlock();
  void ParseSpecparamDecl(std::vector<ModuleItem*>& items);
  void ParseSpecifyItem(std::vector<SpecifyItem*>& items);
  SpecifyItem* ParseSpecifyPathDecl();
  bool ParsePolarityPrefixedParallelPath(SpecifyItem* item);
  void ParseSpecifyPathOperator(SpecifyItem* item);
  void ParseSpecifyPathDestination(SpecifyItem* item);
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
  void ParseSplitEdgeDescriptor(
      char first, SourceLoc tok_loc,
      std::vector<std::pair<char, char>>& descriptors);
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
  bool DotOpensNamedParamAssignment();
  void ParseUseClauseCell(ConfigRule* rule);
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
  void ParseUnionQualifiers(DataType& dtype);
  void ParseStructPackedSigning(DataType& dtype);
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
  bool IsTfPortDeclarationStart();
  Direction ParseTfPortDirection();
  void ParseTfPortDeclarators(ModuleItem* item, const TfPortHeader& hdr);

  uint8_t ParseChargeStrength();
  void ParseDriveStrength(uint8_t& s0, uint8_t& s1);
  void ReportDriveStrengthAfterDelay(const Expr* delay);
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
  // True where the tokens after the leading identifier are one more identifier
  // and a semicolon and nothing else, which is the shape §6.18's undeclared
  // type_identifier and a port-list-less instantiation share.
  bool LooksLikeUndeclaredTypeDecl();
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
  Expr* ParseAssocIndexDim();
  void ParseParenList(std::vector<Expr*>& out);
  std::vector<DataType> ParseTypeParamList();
  DataType ParseOneTypeParam();
  DataType ParseNamedType();

  Stmt* ParseStmt();
  std::string_view TryParseStmtLabel();
  bool RejectMisplacedStmtLabel();
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
  bool AtClockingDecl();
  void RejectClockingDecl(std::string_view message);
  void ParseClockingItemList(ModuleItem* item);
  void ParseClockingItem(ModuleItem* item);
  void ParseClockingDefaultSkews(ModuleItem* item);
  void CheckClockingBlockDecl(const ModuleItem* decl, std::string_view kind);
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
  void WarnUnevaluatedConcurrentAssertion(SourceLoc loc, ModuleItemKind kind);
  ModuleItem* ParseCoverProperty();
  ModuleItem* ParseRestrictProperty();
  ModuleItem* ParsePropertyDecl();
  ModuleItem* ParseSequenceDecl();
  void ScanSequenceBody(ModuleItem* item);
  void ScanSequenceClockEvent(ModuleItem* item);
  void RejectLocalInClockEvent(const ModuleItem* item, std::string_view name);
  void ValidateLiteralCycleDelayRange(SourceLoc range_loc);
  void ValidateCycleDelayMinTypMax(SourceLoc range_loc);
  void ValidateCycleDelayIntegerValue(SourceLoc range_loc);
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
  bool StartsShallowCopySource();
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
  void ParsePatternElement(Expr* pat, bool& named);
  Expr* ParsePatternKeyword();
  Expr* ParsePatternBinding();
  Expr* ParseCastExpr();
  Expr* ParseTypeRefExpr();
  Expr* ParseWithClause(Expr* expr);
  Expr* ParseWithClauseRange();
  std::vector<std::string_view> ParseWithClauseIdentifiers(Expr* expr);
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
  bool AtUnsizedPackedDim(const DataType& dtype);
  void TakeUnsizedPackedDim(DataType& dtype);
  DataType ParseVirtualInterfaceType();

  std::vector<EventExpr> ParseEventList();
  EventExpr ParseSingleEvent();

  std::string_view ParseDottedPath();
  // Consume the next token when it is the one asked for, and report it
  // missing otherwise. Each caller is parsing a different production of the
  // syntax and so enforcing a different rule, so the subclause of IEEE
  // 1800-2023 the report names comes from the caller: a subclause written into
  // either of these two would be right for one caller and wrong for every
  // other. There is no form that omits it.
  Token Expect(TokenKind kind, Subclause subclause);
  Token ExpectIdentifier(Subclause subclause);
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

  // Makes every name of `names` a type name where the parser now stands.
  void AdoptTypeNames(const ScopeTypeNames& names);
  // Applies one package_import_item to what the parser reads as a type name.
  void ApplyImportedTypeNames(const ImportItem& item);
  // Makes the type names of the classes `decl` derives from type names in its
  // own body.
  void AdoptBaseClassTypeNames(const ClassDecl* decl);

  Lexer& lexer_;
  Arena& arena_;
  DiagEngine& diag_;
  std::unordered_set<std::string_view> known_types_;
  std::unordered_set<std::string_view> known_nettypes_;
  std::unordered_set<std::string_view> known_udps_;

  // What each package and each class declared, keyed by its own name and kept
  // after that scope has closed. known_types_ answers what is a type name where
  // the parser stands; these two answer what §26.3's import declaration and
  // §8.13's extends clause can put back into it. They are maps rather than more
  // saved sets because a package's names reach a module that named the package,
  // which is not a containment relation and so is not what TypeNameScope below
  // expresses.
  std::unordered_map<std::string_view, ScopeTypeNames> package_types_;
  std::unordered_map<std::string_view, ScopeTypeNames> class_types_;

  // §23.9 lists the elements that define a new scope: "Modules, Interfaces,
  // Programs, Checkers, Packages, Classes, Tasks, Functions, begin-end blocks
  // (named or unnamed), fork-join blocks (named or unnamed), Generate blocks"
  // (printed page 761 of ~/LRM.pdf). A type name declared inside one is a type
  // name there and not in the design element after it. Constructing this
  // records what known_types_ and known_nettypes_ held on the way in;
  // destroying it puts both back. §6.6.7's ParseNettypeDecl fills the two
  // together, and a nettype name decides how `#` after an identifier is read,
  // so restoring one without the other leaves the leak for that reading.
  //
  // All eleven of that list are guarded: a module, an interface, a program and
  // a checker, plus the extern headers of the first three, at ParseModuleDecl,
  // ParseInterfaceDecl, ParseProgramDecl, ParseCheckerDecl and
  // ParseExternModuleDecl; a task, a function, a begin-end block, a fork-join
  // block and a generate block, at ParseTaskDecl, ParseFunctionDecl,
  // ParseBlockStmt, ParseForkStmt and ParseGenerateBody; and a package and a
  // class, at ParsePackageDecl and ParseClassDecl. The last two guards are what
  // package_types_ and class_types_ above exist for. Closing either scope takes
  // its type names out of known_types_, and §26.3's import declaration and
  // §8.13's extends clause are what put them back, in the scopes the standard
  // says they are visible in and in no others.
  //
  // The last five are guarded for the same reason as the first four, and §23.9
  // is what says a name inside them is never wanted outside. Its search runs
  // upward and only upward: Figure 23-2 on printed page 762 gives block G the
  // scopes containing it and denies it the scopes beside it, and a hierarchical
  // path reaches a variable, a task, a function or a named block rather than a
  // type. A data type is written as a bare or a package-scoped name, so a type
  // declared in one of these five has no spelling that reaches it from outside,
  // the named generate block included.
  //
  // A destructor rather than a save and a restore written at each site, because
  // a parse function has more than one exit and error recovery takes some of
  // them. A restore missed on one path reintroduces the leak for one kind of
  // declaration while every test for the others stays green.
  //
  // Nothing guards the compilation unit itself. §3.12.1 makes a declaration at
  // that scope visible in every design element of the unit, which is what
  // leaving the outermost set alone gives, and it is why the built-in class
  // names the constructor seeds stay visible throughout.
  class TypeNameScope {
   public:
    explicit TypeNameScope(Parser& p)
        : parser_(p),
          saved_types_(p.known_types_),
          saved_nettypes_(p.known_nettypes_) {}
    ~TypeNameScope() {
      parser_.known_types_ = std::move(saved_types_);
      parser_.known_nettypes_ = std::move(saved_nettypes_);
    }
    TypeNameScope(const TypeNameScope&) = delete;
    TypeNameScope& operator=(const TypeNameScope&) = delete;

    // The names registered since this scope opened, which is what the scope's
    // own body declared. Call it before the scope closes: ParsePackageDecl and
    // ParseClassDecl each record the answer so that an import declaration or an
    // extends clause elsewhere can put those names back. A name declared by a
    // scope nested in this one is absent, because that scope's own guard
    // restored it away before this one is asked.
    ScopeTypeNames NamesAddedSoFar() const {
      ScopeTypeNames added;
      for (auto name : parser_.known_types_) {
        if (saved_types_.count(name) == 0) added.types.insert(name);
      }
      for (auto name : parser_.known_nettypes_) {
        if (saved_nettypes_.count(name) == 0) added.nettypes.insert(name);
      }
      return added;
    }

   private:
    Parser& parser_;
    std::unordered_set<std::string_view> saved_types_;
    std::unordered_set<std::string_view> saved_nettypes_;
  };
  ModuleDecl* current_module_ = nullptr;
  PackageDecl* current_package_ = nullptr;
  CompilationUnit* current_compilation_unit_ = nullptr;
  bool InProgramBlock() const {
    return current_module_ &&
           current_module_->decl_kind == ModuleDeclKind::kProgram;
  }

  int generate_block_depth_ = 0;
  bool InGenerateBlock() const { return generate_block_depth_ > 0; }

  // How many of §18.17's rs_code_block are open around the statement being
  // read. A.6.12 gives `rs_code_block ::= { { data_declaration }
  // { statement_or_null } }`, so the block a statement stands in is closed by a
  // right brace rather than by a keyword, and the statement loops of
  // Parser::ParseBlockStmt and Parser::ParseForkStmt have to stop at one to
  // leave it for Parser::ParseRsCodeBlockStmts. The count is what tells that
  // brace from the one closing a concatenation under §11.4.12 or an assignment
  // pattern under §10.9, neither of which any statement loop ever meets: both
  // are consumed by the expression that opened them.
  int rs_code_block_depth_ = 0;
  bool ClosesOpenRsCodeBlock(TokenKind tk) const {
    return tk == TokenKind::kRBrace && rs_code_block_depth_ > 0;
  }

  bool in_generate_region_ = false;

  // §H.2: true while the formal argument list of a DPI import declaration is
  // being parsed. Leaving a packed range unspecified is a relaxation granted to
  // those formals alone, so the "[]" packed form is recognized only here.
  bool in_dpi_import_formals_ = false;

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
