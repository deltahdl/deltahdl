#pragma once

#include <cstddef>
#include <cstdint>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "lexer/lexer.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_covergroup.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "parser/param_port_list.h"
#include "parser/scope_prefix_record.h"
#include "parser/scope_type_names.h"
#include "parser/udp_ansi_port_entry.h"

namespace delta {

class TypeNameScope;
struct CovergroupBodyState;
struct DataDeclQualifiers;
struct TfPortHeader;

inline constexpr char kAnonymousProgramItemsMessage[] =
    "an anonymous program may contain only task, function, class, interface "
    "class, covergroup, and class constructor declarations";

class Parser {
 public:
  Parser(Lexer& lexer, Arena& arena, DiagEngine& diag);

  CompilationUnit* Parse();
  CompilationUnit* ParseLibraryText();

  void AdoptCompilationUnitScope(const CompilationUnitScopeNames& names);
  CompilationUnitScopeNames CompilationUnitScope() const;

  bool EndedInsideDeclaration() const { return ended_inside_declaration_; }

 private:
  friend void ParseGateInstanceTail(Parser& p, ModuleItem* item, bool has_name);
  friend class TypeNameScope;
  friend struct ParserStmtHelpers;
  friend struct ParserPortHelpers;
  friend struct ParserParamPortHelpers;
  friend struct ParserDpiHelpers;
  friend struct ParserAssertHelpers;
  friend struct ParserPropertySpecHelpers;
  friend struct ParserPropertyGrammar;
  friend struct ParserSeqLinearHelpers;
  friend struct ParserClassHelpers;
  friend struct ParserClassHeaderHelpers;
  friend struct ParserConstraintItemHelpers;
  friend struct ParserDataDeclHelpers;
  friend struct ParserClassOverrideHelpers;
  friend struct ParserConfigHelpers;
  friend struct ParserExpectAccess;

  void ParseTopLevel(CompilationUnit* unit);
  void ReportUnexpectedTopLevelToken();
  bool TryParsePrimaryTopLevel(CompilationUnit* unit);
  bool TryParseAnonymousProgram(CompilationUnit* unit);
  void ParseExternTopLevel(CompilationUnit* unit);
  bool TryParseSecondaryTopLevel(CompilationUnit* unit);
  bool TryParseCuScopeDataDecl(CompilationUnit* unit);
  bool StaticOpensConstraint();
  bool AtScopedIdentifier();
  bool TryParseCuScopeItem(CompilationUnit* unit);
  bool TryParseCuImportOrExportDecl(CompilationUnit* unit);
  void ParseOutOfBlockConstraint(CompilationUnit* unit,
                                 const std::vector<ModuleItem*>* scope_items);
  bool TryParseExternConstraintItem(std::vector<ModuleItem*>& items);

  ModuleDecl* ParseModuleDecl();
  ModuleDecl* ParseExternModuleDecl();
  ModuleDecl* ParseExternInterfaceOrProgramDecl();
  ModuleDecl* TryParseNestedExternDecl(SourceLoc extern_loc);
  PackageDecl* ParsePackageDecl();
  bool TryParsePackageBodyItem(std::vector<ModuleItem*>& items);
  void ParseImportDecl(std::vector<ModuleItem*>& items);
  ModuleItem* ParseImportItem();
  void ParseExportDecl(std::vector<ModuleItem*>& items);
  ModuleItem* ParseDpiImport();
  ModuleItem* ParseDpiExport(SourceLoc loc);
  void ParsePortList(ModuleDecl& mod);
  void ParseOnePortOfList(ModuleDecl& mod, const PortDecl* prev,
                          bool is_checker);
  void DiagnoseCheckerFormalAsWritten(const PortDecl& port);
  Expr* ParseCheckerFormalDefault();
  void ParseNonAnsiPortList(ModuleDecl& mod);
  PortDecl ParsePortDecl(bool is_checker);
  void ParseModuleBody(ModuleDecl& mod);
  bool TryParseBodyPortDecl(ModuleDecl& mod);
  void ParseNonAnsiPortDecls(ModuleDecl& mod,
                             std::vector<Attribute> attrs = {});
  void ParseModuleItem(std::vector<ModuleItem*>& items);
  std::string_view TryParseAssertionItemLabel();
  void ParseDataDeclItem(std::vector<ModuleItem*>& items, size_t before,
                         const std::vector<Attribute>& attrs);
  bool TryParseTypeRef(std::vector<ModuleItem*>& items);
  bool TryParseProcessBlock(std::vector<ModuleItem*>& items);
  bool TryParseKeywordItem(std::vector<ModuleItem*>& items);
  bool TryParseDeclKeywordItem(std::vector<ModuleItem*>& items);
  void RejectInCheckerBody(const char* msg);
  void RejectInProgramBody(SourceLoc loc, const char* msg);
  void RejectInInterfaceBody(const char* msg);
  void RejectMisplacedGate();
  void RejectInPackageBody(const char* msg);
  void RejectAttributesBeforeItem(SourceLoc attr_loc);
  void FilterPackageItems(std::vector<ModuleItem*>& items, size_t before);
  bool TryRejectBodyPortDecl();
  bool TryParseSpecifyItem(std::vector<ModuleItem*>& items);
  ModuleItem* ParseExternTfDeclaration(SourceLoc extern_loc);
  bool AtMisplacedMethodQualifier();
  void RejectMisplacedMethodQualifier(std::vector<ModuleItem*>& items);
  bool TryParseMiscKeywordItem(std::vector<ModuleItem*>& items);
  void RejectProceduralContinuousAssignItem();
  void ParseTimeunitItem();
  bool NoteItemAndMatchNull(bool& has_read_item);
  void ParseInterconnectItem(std::vector<ModuleItem*>& items);
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
  void ParseParamPortDecls(ParamPortList& out);
  void ParseParamsPortsAndSemicolon(ModuleDecl& decl);

  void ParseGenerateRegion(std::vector<ModuleItem*>& items);
  void ParseGenerateBody(std::vector<ModuleItem*>& body,
                         std::string_view& out_label, bool& out_has_begin_end,
                         bool else_may_follow);
  ModuleItem* ParseGenerateFor();
  Stmt* ParseGenvarInitialization();
  Stmt* ParseGenvarIteration(std::string_view genvar);
  void MatchEndBlockLabel(std::string_view inline_label,
                          std::string_view prefix_label);
  ModuleItem* ParseGenerateIf();
  void ParseGenerateCaseLabel(GenerateCaseItem& ci);
  ModuleItem* ParseGenerateCase();

  ModuleDecl* ParseInterfaceDecl();
  ModuleDecl* ParseProgramDecl();
  void ParseModportDecl(std::vector<ModportDecl*>& out);
  void ParseModportItem(ModportDecl* mp);
  struct ModportScan {
    enum class Opened : uint8_t { kNothing, kSimple, kTf, kClocking };
    Opened opened = Opened::kNothing;
    Direction dir = Direction::kNone;
    bool is_import = false;
  };
  void ParseModportPortEntry(ModportDecl* mp, ModportScan& scan);
  void ParseModportPrototypeSpecifiers(ModuleItem* item);
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
  void ParseClassParameterMembers(std::vector<ClassMember*>& members,
                                  ClassMember* member);
  bool TryParseKeywordClassMember(std::vector<ClassMember*>& members,
                                  ClassMember* member, bool proto);
  bool ParseClassQualifiers(ClassMember* member);
  enum ClassQualifier : uint16_t {
    kQualRand = 1,
    kQualRandc = 2,
    kQualStatic = 4,
    kQualProtected = 8,
    kQualLocal = 16,
    kQualVirtual = 32,
    kQualPure = 64,
    kQualConst = 128,
    kQualExtern = 256,
  };
  void RejectMisplacedClassQualifiers(const ClassMember& member,
                                      uint16_t allowed, const char* item);
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
  void ScanConstraintBodyRelations(ClassMember* member, bool inline_block);
  ClassMember* CaptureInlineConstraintBlock();
  bool ScanConstraintBodyToken(ClassMember* member, int& depth, bool& in_soft,
                               bool carried_qualifier);
  void CaptureConstraintRelation(ClassMember* member);
  void CaptureSoftConstraintRelation(ClassMember* member);
  void CaptureDisableSoftConstraint(ClassMember* member);
  bool TryCaptureBracedImplication(ClassMember* member);
  struct ImpliedRelation;
  Expr* ParseImpliedRelation(Expr* antecedent, bool& soft);
  bool ParseImpliedSet(Expr* antecedent, std::vector<ImpliedRelation>& out);
  bool TryCaptureDist(ClassMember* member, bool is_soft = false);
  bool ParseDistItem(ConstraintDistItem& item);
  bool ParseDistRange(ConstraintDistItem& item);
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
  bool AtSelectBracket();
  bool in_sequence_body_ = false;
  void CaptureClockedBooleanPropertyBody(ModuleItem* item);
  bool PropertyBodyHasTemporalOperator();
  void CheckConstraintExprToken(const Token& tok);
  void CheckForeachConstraintHeader(ClassMember* member);
  void CaptureForeachConstraintBody(std::vector<Expr*>& body);
  void CheckSolveBeforeConstraint(ClassMember* member);
  void ParseSolveBeforeList(std::vector<ConstraintSolveBeforeEntry>& out);
  bool CheckDistDefault(SourceLoc loc, int& default_count);
  void CheckDistSet();
  std::pair<uint8_t, uint8_t> ParseGateStrength(GateKind kind, SourceLoc loc);
  bool IsAtGateKeyword();
  void ParseGateInst(std::vector<ModuleItem*>& items);
  void ParseInlineGateTerminals(GateKind kind, SourceLoc loc,
                                std::vector<ModuleItem*>& items);
  ModuleItem* ParseOneGateInstance(GateKind kind, SourceLoc loc);
  void ParseInstanceRange(ModuleItem* item, bool first);
  uint8_t ParseStrength0();
  uint8_t ParseStrength1();
  void ParseGateDelay(Expr*& d1, Expr*& d2, Expr*& d3);
  Expr* ParseDelayValue();
  Expr* ParsePathpulseLimits(Expr*& error_limit);

  UdpDecl* ParseUdpDecl();
  bool UdpPortListIsDeclarations();
  UdpAnsiPortEntry ParseUdpAnsiPortEntry();
  void ParseUdpAnsiHeader(UdpDecl* udp);
  void ParseUdpNonAnsiHeader(UdpDecl* udp);
  void ParseUdpInitialStatement(UdpDecl* udp);
  UdpDecl* ParseExternUdpDecl();
  void ParseUdpParenEdge(UdpTableRow& row);
  Expr* ParseUdpOutputInitialValue(bool declares_reg);
  void ParseUdpOutputDecl(UdpDecl* udp);
  void ParseUdpPortDecls(UdpDecl* udp);
  void ParseUdpTable(UdpDecl* udp);
  void ParseUdpTableRow(UdpDecl* udp, bool& reg_mismatch_reported,
                        bool& row_width_reported);

  void RejectUdpPortDimension();

  void RejectUdpInoutPort();
  void RejectUdpInitialValueOn(const char* declaration);
  void AppendUdpInputSymbols(UdpTableRow& row, const Token& tok);
  char ParseUdpFieldSymbol();
  void ParseUdpInputDecl(UdpDecl* udp);

  void ValidateUdpHeader(UdpDecl* udp);
  bool AtUdpOnlyInstanceForm();
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
  enum class CovItemLevel : uint8_t { kCoverpoint, kCross };
  void ParseCoverageFormalList(std::vector<FunctionArg>& args,
                               std::string_view output_message,
                               Subclause subclause);
  void ParseCovergroupFormals(CovergroupBodyState& state);
  void ParseCoverageEvent(CovergroupBodyState& state);
  void ParseSampleFunctionEvent(CovergroupBodyState& state);
  void ParseBlockEventExpression(std::vector<BlockEventTerm>& terms);
  void ParseHierarchicalBtfIdentifier(std::vector<std::string_view>& path);
  void ParseCovergroupItem(CovergroupBodyState& state);
  void ParseLabelledCoverageSpec(CovergroupBodyState& state,
                                 const DataType* data_type);
  void RejectCovergroupItem();
  bool ParseCoverageOption(CoverageOption& option);
  void ParseCovergroupOption(CovergroupBodyState& state);
  bool ParseItemLevelOption(CoverageOption& option,
                            const CovergroupBodyState& state,
                            CovItemLevel level);
  void RejectFormalInTypeOption(const CoverageOption& option,
                                const CovergroupBodyState& state);
  void TakeCoverageName(CovergroupBodyState& state, std::string_view name,
                        SourceLoc loc);
  bool IdentifierOpensCoverageLabel();
  bool IdentifierOpensCoverPointWith();
  DataType ParseCoverpointDataType();
  bool BraceOpensCoverpointBody();
  Expr* ParseCoverpointHead();
  Expr* ParseCoverageIffGuard();
  void ParseCoverPoint(CovergroupBodyState& state, std::string_view label,
                       SourceLoc label_loc, const DataType* data_type);
  bool OpensCoverageBodyItem();
  void SkipCoverageItemTail();
  void ExpectCoverageItemEnd();
  void ExpectCoverageCloseParen();
  bool ParseBinsOrOptions(BinsOrOptions& bins, CovergroupBodyState& state);
  void ParseBinsValue(BinsOrOptions& bins);
  void ParseCovergroupRangeList(std::vector<CovergroupValueRange>& ranges);
  CovergroupValueRange ParseCovergroupValueRange();
  bool AtTransRepetition();
  TransRangeList ParseTransRangeList();
  void ParseTransList(std::vector<TransSet>& sets);
  void CheckTransitionBins(const BinsOrOptions& bins);
  void ParseCoverCross(CovergroupBodyState& state, std::string_view label,
                       SourceLoc label_loc);
  void ValidateCrossItemList(std::vector<CrossItem>& items);
  void ParseCrossBody(CoverCrossDecl& cross, CovergroupBodyState& state);
  void ParseCrossBodyItem(CoverCrossDecl& cross, CovergroupBodyState& state);
  bool ParseBinsSelection(BinsSelection& bins);
  SelectExpression* NewSelectExpression(SelectExpressionKind kind,
                                        SourceLoc loc);
  SelectExpression* ParseSelectExpression();
  SelectExpression* ParseSelectConjunction();
  SelectExpression* ParseSelectPostfix();
  SelectExpression* ParseSelectPrimary();
  SelectExpression* ParseSelectCondition();
  void ParseSelectMatches(SelectExpression& select);
  bool IdentifierIsCrossName();

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
  bool RefusePathpulseTerminalSelect();
  void ParsePathPorts(std::vector<SpecifyTerminal>& ports);
  SpecifyTerminal ParseSpecifyTerminal();
  void ParsePathDelays(std::vector<Expr*>& delays);
  void ParsePathDelayList(std::vector<Expr*>& delays);
  bool TryParseParenthesizedPathDelays(std::vector<Expr*>& delays);
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
  void ParseTimingCheckNotifier(TimingCheckDecl& tc);
  void ParseExtendedTimingCheckArgs(TimingCheckDecl& tc);
  void ParseTimeskewExtendedArgs(TimingCheckDecl& tc);
  void ParseSetupholdExtendedArgs(TimingCheckDecl& tc);
  void ParseOptionalDelayedRef(std::string_view& name, Expr*& expr,
                               std::string_view production);

  LibraryDecl* ParseLibraryDecl();
  IncludeStmt* ParseLibraryIncludeStmt();
  Token ParseFilePathSpec();
  SourceLoc ParseFilePathSpecList(std::vector<std::string_view>& paths);
  bool MatchIncdirOption();
  std::string_view ArenaCopy(std::string_view text);
  void ParseBindItem(std::vector<ModuleItem*>& items);
  BindDirective* ParseBindDirective();
  bool TryParseCuTypeDeclaration(CompilationUnit* unit);
  bool TryParseUnitBindDirective(CompilationUnit* unit);
  BindTargetInstance ParseBindTargetInstance();

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
  void ParseNettypeWithClause(ModuleItem* item);
  DataType ParseEnumType();
  DataType ParseEnumBody(const DataType& base);
  Expr* ParseEnumRangeBound();
  DataType ParseStructOrUnionType();
  void ParseUnionQualifiers(DataType& dtype);
  void ParseStructPackedSigning(DataType& dtype);
  void ParseStructMembers(DataType& dtype);
  DataType ParseStructMemberType();
  void ParseStructMemberList(DataType& dtype, const DataType& member_type,
                             const std::vector<Attribute>& member_attrs,
                             bool is_rand, bool is_randc);
  DataType ParseFunctionReturnType();
  bool TryParseInlineAggregateType(DataType& dt);
  void ParseDynamicOverrideSpecifiers(ModuleItem* item);
  Direction ParseArgDirection(FunctionArg& arg, Direction sticky_dir,
                              bool* was_explicit = nullptr);
  void ParseFuncName(ModuleItem* item);
  void ParseFuncBody(ModuleItem* item);
  ModuleItem* ParseFunctionDecl(bool prototype_only = false);
  ModuleItem* ParseTaskDecl(bool prototype_only = false);
  struct FuncArgScan {
    bool constructor_args = false;
    Direction sticky_dir = Direction::kInput;
    bool seen_default = false;
    DataType prev_data_type;
    bool first_arg = true;
    bool prev_was_default = false;
  };
  std::vector<FunctionArg> ParseFunctionArgs(bool require_identifiers = true,
                                             bool constructor_args = false);
  bool TryParseDefaultArgSentinel(std::vector<FunctionArg>& args,
                                  FuncArgScan& scan);
  void ParseFunctionArgTrailer(FunctionArg& arg, bool require_identifiers);
  void ParseOneFunctionArg(std::vector<FunctionArg>& args, FuncArgScan& scan,
                           bool require_identifiers);
  bool TryParseTfPortDeclaration(ModuleItem* item,
                                 std::unordered_set<std::string_view>& untyped);
  void ParseSubroutineBody(ModuleItem* item, TokenKind end_kw,
                           Subclause subclause);
  bool IsTfPortDeclarationStart();
  Direction ParseTfPortDirection();
  void ParseTfPortDeclarators(ModuleItem* item, const TfPortHeader& hdr);

  uint8_t ParseChargeStrength();
  void ParseDriveStrength(uint8_t& s0, uint8_t& s1);
  void ReportDriveStrengthAfterDelay(const Expr* delay,
                                     std::string_view subclause = "10.3.4");
  void ParseNetStrength(DataType& dtype);
  void ParseVectoredScalared(DataType& dtype);
  void ParseVarDeclList(std::vector<ModuleItem*>& items, const DataType& dtype);
  void ParseContinuousAssign(std::vector<ModuleItem*>& items);
  ModuleItem* ParseAlias();
  void ParseParamDecl(std::vector<ModuleItem*>& items);
  void ParseImplicitParamRange(DataType& dtype);
  void ParseTypeParamDecl(std::vector<ModuleItem*>& items, SourceLoc loc,
                          bool localparam = false);
  DataTypeKind ParseTypeParamRestriction();
  ModuleItem* ParseAlwaysBlock(AlwaysKind kind);
  ModuleItem* ParseInitialBlock();
  ModuleItem* ParseFinalBlock();
  void ParseVarPrefixed(std::vector<ModuleItem*>& items, bool is_const);
  void ParseTypedItemOrInst(std::vector<ModuleItem*>& items,
                            const DataDeclQualifiers& quals);
  void ParseImplicitTypeOrInst(std::vector<ModuleItem*>& items);
  void RejectInstInProgram(SourceLoc loc, std::string_view cell,
                           const char* msg);
  void ParseScopedTypeOrInst(const Token& name_tok,
                             std::vector<ModuleItem*>& items);
  bool LooksLikeScopedInstTail();
  bool AtCheckerInstantiationStmt();
  Stmt* ParseCheckerInstantiationStmt();
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
  Expr* ParsePortActual();
  void RecordTriggeredRead(const Expr* base);
  void ParseUnpackedDims(std::vector<Expr*>& dims);
  Expr* ParseAssocIndexDim();
  void ParseParenList(std::vector<Expr*>& out);
  std::vector<DataType> ParseTypeParamList();
  DataType ParseOneTypeParam();
  DataType ParseNamedType();
  void ParseTypeScopePath(DataType& dtype, bool assignment_written);

  Stmt* ParseStmt();
  std::string_view TryParseStmtLabel();
  bool RejectMisplacedStmtLabel();
  Stmt* ParseStmtBody(std::string_view prefix_label = {});
  Stmt* ParseBlockStmt(std::string_view prefix_label = {});
  Stmt* ParseIfStmt();
  Stmt* ParseCaseStmt(TokenKind case_kind);
  CaseItem ParseCaseItem(bool inside = false, bool matches = false);
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
  Stmt* ParseVoidCastCallStmt();
  Stmt* ParseAssignmentOrExprStmt();
  Stmt* ParseAssignmentOrExprNoSemi();
  void SkipUnparenthesizedAssignInExpr();
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
  bool AtScopedTypeName();
  bool IsScopedCallOrAssignStmt();
  void ParseBlockVarDecls(std::vector<Stmt*>& stmts);
  void ParseBlockDataDecl(std::vector<Stmt*>& stmts,
                          const std::vector<Attribute>& attrs);

  ModuleItem* ParseClockingDecl();
  bool AtClockingDecl();
  void RejectClockingDecl(std::string_view message);
  void ParseClockingItemList(ModuleItem* item);
  void ParseClockingItem(ModuleItem* item);
  void ParseClockingDefaultSkew(const Token& direction, Edge& edge,
                                Expr*& delay);
  void ParseClockingDefaultSkews(ModuleItem* item);
  void CheckClockingBlockDecl(const ModuleItem* decl, std::string_view kind);
  void ParseClockingSkew(Edge& edge, Expr*& delay);
  Direction ParseClockingDirection(Edge& in_edge, Expr*& in_delay,
                                   Edge& out_edge, Expr*& out_delay);
  Expr* ParseWaitOrderOperand();
  Stmt* ParseWaitOrderStmt();

  Stmt* ParseImmediateAssert();
  Stmt* ParseImmediateAssume();
  Stmt* ParseImmediateAssertLike(StmtKind kind, TokenKind keyword);

  Stmt* ParseProceduralConcurrentAssertLike(StmtKind kind);
  Stmt* ParseProceduralPropertySpec(StmtKind kind, SourceLoc loc,
                                    Subclause subclause, bool sequence);
  ModuleItem* ParseDeferredImmediateItem(SourceLoc loc, StmtKind kind);
  Stmt* ParseExpectStmt();
  Stmt* ParseImmediateCover();
  ModuleItem* ParseAssertProperty();
  ModuleItem* ParseAssumeProperty();
  ModuleItem* ParsePropertyAssertLike(ModuleItemKind kind, TokenKind keyword);
  bool TryParseDisableIff(Expr*& disable_iff);
  bool ParseSequenceExprInto(ModuleItem* item);
  bool ParseSequenceTermInto(ModuleItem* item);
  bool TryParseSimpleConcurrentProperty(ModuleItem* item, StmtKind body_kind);
  bool TryParsePropertyInstanceSpec(ModuleItem* item);
  bool ReadStaticPropertySpec(ModuleItem* item, StmtKind body_kind);
  bool BodyHasTemporalOperator();
  void WarnUnevaluatedConcurrentAssertion(SourceLoc loc);
  ModuleItem* ParseCoverProperty();
  ModuleItem* ParseRestrictProperty();
  ModuleItem* ParsePropertyDecl();
  ModuleItem* ParseSequenceDecl();
  void ScanSequenceBody(ModuleItem* item);
  void ScanSequenceClockEvent(ModuleItem* item);
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
  void ParseListOfArguments(Expr* call);
  void ParseCallArgs(Expr* call);
  Expr* ParseTypeOr(Expr* (Parser::*read)());
  void ParseTrailingNamedArgs(Expr* call);
  Expr* ParseMemberAccessChain(Token tok);
  bool StartsShallowCopySource();
  Expr* MakeMemberAccess(Expr* base);
  void ParseParamValueAssignment(Expr* base);
  Expr* ParseParameterizedScope(Expr* base);
  Expr* ParseScopeSpecialization(Expr* base);
  Expr* TryParseUserTypeCast(const Token& tok);
  Expr* ParseIdentifierExpr();
  Expr* ParseLocalScopeExpr();
  Expr* TryParseIdentifierCast(Expr* base, bool* handled);
  Expr* ParseMethodTail(Expr* root);
  Expr* ParseParenMethodTail(Expr* paren);
  Expr* ParseIdentifierPostfixChain(Expr* result);
  Expr* ParseNameTail(Expr* result);
  Expr* ParseWithClauseTail(Expr* result);
  Expr* ParseSelectExpr(Expr* base);
  Expr* ParseSystemCall();
  Expr* ParseUnitScopedName(const Token& unit_tok);
  Expr* MakeSysScopePrefix(const Token& sys_tok);
  Expr* ParseSysRootTail(Expr* expr);
  void ParseSysClockingEventArg(Expr* call);
  void ParseSysCallArgs(Expr* call);
  Expr* ParseConcatenation();
  Expr* ParseAssignmentPattern();
  Expr* ParsePatternReplication(Expr* count, SourceLoc loc);
  void ParsePatternElement(Expr* pat, bool& named);
  Expr* ParsePatternKeyword();
  Expr* ParseDotPattern();
  Expr* ParseCastExpr();
  Expr* ParseTypeRefExpr();
  Expr* ParseWithClause(Expr* expr);
  Expr* ParseWithClauseRange(bool in_stream_expression);
  void ParseRandomizeWith(Expr* call);
  Expr* ParseParenExpr();
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
  DataType ParseTypeAssignmentValue();
  DataType ParseDeclaredDataType();
  bool AtDataTypeOrVoid();
  bool TryParseNetDataType(DataType& dtype, bool has_intervening);
  void ParsePackedDims(DataType& dtype);
  bool AtUnsizedPackedDim(const DataType& dtype);
  void TakeUnsizedPackedDim(DataType& dtype);
  DataType ParseVirtualInterfaceType();
  std::vector<EventExpr> ParseEventList();
  bool OpensEventGroup(bool edges_only);
  EventExpr ParseSingleEvent();
  EventExpr ParseNamedClockingEvent();

  std::string_view ParseDottedPath();
  Token Expect(TokenKind kind, Subclause subclause);
  Token ExpectIdentifier(Subclause subclause);
  bool TryTakeIllFormedSimpleIdentifier(Token* out);
  void MatchEndLabel(std::string_view name);
  bool CheckIdentifier();
  bool Match(TokenKind kind);
  Token Consume();
  Token CurrentToken();
  bool Check(TokenKind kind);
  bool AtDollarEndingRange();
  bool AtEnd();
  SourceLoc CurrentLoc();
  void Synchronize();
  bool ReportedAtEnd(size_t first_report);
  void SynchronizeWithProgress();

  void AdoptTypeNames(const ScopeTypeNames& names);
  void ApplyImportedTypeNames(const ImportItem& item);
  void AdoptBaseClassTypeNames(const ClassDecl* decl);
  void AdoptMethodClassTypeNames(std::string_view class_name);

  Lexer& lexer_;
  Arena& arena_;
  DiagEngine& diag_;
  std::unordered_set<std::string_view> triggered_names_;
  std::vector<TimeLiteralSite> time_literals_;
  ScopePrefixRecord scope_prefixes_;
  std::unordered_set<std::string_view> known_types_;
  std::unordered_set<std::string_view> known_nettypes_;
  std::unordered_set<std::string_view> known_udps_;
  std::unordered_set<std::string_view> declared_design_elements_;

  std::unordered_map<std::string_view, ScopeTypeNames> package_types_;
  std::unordered_map<std::string_view, ScopeTypeNames> class_types_;

  ModuleDecl* current_module_ = nullptr;
  PackageDecl* current_package_ = nullptr;
  CompilationUnit* current_compilation_unit_ = nullptr;
  bool InProgramBlock() const;
  bool InModuleBody() const;
  bool InInterfaceBody() const;
  bool InCheckerBody() const;
  bool InPackageBody() const;
  int generate_block_depth_ = 0;
  bool InGenerateBlock() const { return generate_block_depth_ > 0; }
  bool in_generate_region_ = false;
  void ParseGenerateItem(std::vector<ModuleItem*>& items);

  int rs_code_block_depth_ = 0;
  bool ClosesOpenRsCodeBlock(TokenKind tk) const {
    return tk == TokenKind::kRBrace && rs_code_block_depth_ > 0;
  }

  int always_or_initial_depth_ = 0;
  int cover_pass_statement_depth_ = 0;
  int pattern_depth_ = 0;
  int constraint_block_depth_ = 0;

  bool in_dpi_import_formals_ = false;
  int class_body_depth_ = 0;
  int package_body_depth_ = 0;
  bool in_cu_scope_param_ = false;
  bool in_anonymous_program_ = false;
  bool ended_inside_declaration_ = false;
  bool ForceLocalparam() const {
    return InGenerateBlock() || class_body_depth_ > 0 ||
           package_body_depth_ > 0 || in_cu_scope_param_;
  }
};

}  // namespace delta
