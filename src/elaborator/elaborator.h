#pragma once

#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/compilation_unit_set.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_bind_scope.h"
#include "elaborator/elaborator_data.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_classes.h"
#include "elaborator/elaborator_validate_operations.h"
#include "elaborator/pending_generate.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

class Arena;
class DiagEngine;
struct ContTargetLeaf;
struct Expr;

class Elaborator : public ElaboratorClassRules {
 public:
  struct ParamOverride {
    std::string_view name;
    int64_t value = 0;
    const Expr* value_expr = nullptr;
    std::optional<double> real{};
  };

  using ParamList = std::vector<ParamOverride>;

  Elaborator(Arena& arena, DiagEngine& diag, CompilationUnit* unit);
  Elaborator(Arena& arena, DiagEngine& diag,
             const std::vector<CompilationUnit*>& units);

  RtlirDesign* Elaborate(std::string_view top_module_name);

  RtlirDesign* Elaborate(const std::vector<std::string_view>& top_names);

  RtlirDesign* Elaborate(const ConfigDecl* cfg);

  void SetLibraryDeclarationOrder(std::vector<std::string> order);

  void SetMaxGenerateIterations(int64_t max_iterations);

 private:
  friend struct ItemElaborationStateSaver;
  friend struct UnitScopeTables;

  void RunPreElaborationValidations();

  RtlirDesign* ElaborateTops(const std::vector<ModuleDecl*>& top_decls);
  bool ElaborateTopModules(const std::vector<ModuleDecl*>& top_decls,
                           RtlirDesign* design);
  void ResolveDefparamsAndGenerates(RtlirDesign* design);

  void ValidateNameSpaces();

  void ValidateConfigDesignStatements();

  void ValidateConfigDefaultClauses();

  void ValidateConfigInstanceClauses();

  void ValidateConfigCellClauses();

  void ValidateConfigPackageBinding();

  void ValidateConfigHierarchicalRules();

  void ValidateConfigLocalparams();

  void ValidateConfigParamOverrides();

  void CollectConfigInstanceParamOverrides(const ConfigDecl* cfg);
  void CollectConfigCellClauseOverrides(const ConfigDecl* cfg);
  void CollectConfigInstanceBindOverrides(const ConfigDecl* cfg);
  void CollectConfigRuleTables(const ConfigDecl* cfg);
  void CollectCellUseOverride(const ConfigDecl* cfg, const ConfigRule* rule);
  const ConfigDecl* DelegatedConfigFor(std::string_view cell) const;
  void EnterDelegatedConfig(const ConfigDecl* inner);
  void LeaveDelegatedConfig();

  void ValidateAnonymousProgramNameSharing();

  void ValidateAnonymousProgramHierRefs();

  void ValidatePackageItems();

  void ValidatePackageReferences();

  void ValidatePackageExports();

  void ValidatePackageImportRules(const ModuleDecl* decl);

  void ValidateHierRefToImportedName(const ModuleDecl* decl,
                                     const RtlirModule* mod);

  void ApplyCompilationUnitImports(const ModuleDecl* decl, RtlirModule* mod);
  void ApplyHeaderImports(const ModuleDecl* decl);
  void ApplyBodyImport(const ImportItem& import_item);

  void ValidateModports();

  void ValidateSpecifyBlocks();

  void RegisterCuScopeItems();

  void ResolveExternModules();

  ModuleDecl* FindModule(std::string_view name) const;
  ModuleDecl* SearchModule(std::string_view name) const;
  ModuleDecl* FindDesignCell(std::string_view library,
                             std::string_view cell) const;

  std::optional<ModuleDecl*> ResolveCellUseOverride(
      std::string_view name, const ModuleDecl* found) const;

  std::optional<ModuleDecl*> ResolveInstanceBindOverride() const;

  ModuleDecl* FindModuleInScope(std::string_view name) const;

  void ReportUndeclaredTypeName(const ModuleItem* item);
  RtlirModule* ElaborateModule(const ModuleDecl* decl, const ParamList& params);

  void ElaborateParamPortList(const ModuleDecl* decl, const ParamList& params,
                              RtlirModule* mod);

  void ElaboratePorts(const ModuleDecl* decl, RtlirModule* mod);

  void ElaborateItem(ModuleItem* item, RtlirModule* mod);
  bool ElaborateDeclItem(ModuleItem* item, RtlirModule* mod);
  void ElaborateModuleClassDecl(ModuleItem* item, RtlirModule* mod);
  bool ElaborateBehavioralItem(ModuleItem* item, RtlirModule* mod);
  void AddProcedure(ModuleItem* item, RtlirModule* mod, RtlirProcessKind kind);
  void AddInferenceCallees(const Stmt* body);
  void ResolveStaticAssertionClock(ModuleItem* item,
                                   const std::vector<EventExpr>& default_clock);
  bool ElaborateAssertionItem(ModuleItem* item, RtlirModule* mod);

  void ElaborateSequenceDeclItem(ModuleItem* item, RtlirModule* mod);
  void ElaboratePropertyDeclItem(ModuleItem* item, RtlirModule* mod);
  void CheckPropertyOperandInstances(const ModuleItem* item);
  void ElaborateAssertPropertyItem(ModuleItem* item, RtlirModule* mod);
  void ElaborateParamDecl(ModuleItem* item, RtlirModule* mod);
  void ElaborateNetDecl(ModuleItem* item, RtlirModule* mod);
  bool ElaborateUserNettypeNet(ModuleItem* item, RtlirModule* mod);

  void ElaborateVarDecl(ModuleItem* item, RtlirModule* mod);
  std::string_view ResolveVarDeclTypeRefs(ModuleItem* item, RtlirModule* mod);
  bool ReconcilePartialPort(std::string_view name, bool decl_signed,
                            NetType net_type, RtlirModule* mod);
  void SetVariableTypeInfo(const ModuleItem* item, RtlirVariable& var,
                           const ScopeMap& scope);
  void NameAdoptedArrayTypedef(const ModuleItem* item,
                               std::string_view typedef_name,
                               RtlirVariable& var);
  void ElaborateContAssign(ModuleItem* item, RtlirModule* mod);
  void ValidateGeneratedItem(const ModuleItem* item, const RtlirModule& mod);
  void RecordProcTarget(std::string_view name, SourceLoc loc);
  void ReportForcesOverMixture(std::string_view declared,
                               std::string_view name);
  void ValidateSubroutineBodyTargets(const ModuleItem* item,
                                     const RtlirModule& mod,
                                     const ScopeMap& scope);
  void ResolvePackedStructParam(RtlirParamDecl& pd, const DataType* type,
                                const Expr* default_value,
                                const ScopeMap& scope);
  void ReportProceduralNetTargets(
      const std::unordered_map<std::string_view, SourceLoc>& targets);
  void RecordGateOutputDrivers(const ModuleItem* item);
  bool ValidateContAssignLeaves(ModuleItem* item, RtlirModule* mod,
                                const std::vector<ContTargetLeaf>& leaves);
  bool ValidateContAssignLeaf(ModuleItem* item, RtlirModule* mod,
                              const ContTargetLeaf& leaf,
                              const ScopeMap& scope);
  void ValidateContAssignVarLeaf(ModuleItem* item, std::string_view name);
  void ValidateContAssignIdentLhs(std::string_view name, ModuleItem* item,
                                  RtlirModule* mod);
  void ValidateContAssignDriveStrength(ModuleItem* item, RtlirModule* mod);
  void ElaborateSpecparam(ModuleItem* item, RtlirModule* mod);

  void ElaborateTypedef(ModuleItem* item, RtlirModule* mod);
  void ValidateTypedefShape(const DataType& dtype, SourceLoc loc,
                            const ScopeMap* member_default_scope);
  void ValidateCuTypedefs();

  void ElaborateNettypeDecl(ModuleItem* item, RtlirModule* mod);
  void RegisterNettypeResolutionAndCanonical(const ModuleItem* item);
  void CheckNettypeResolutionFunction(const ModuleItem* item);

  void ElaborateItems(const ModuleDecl* decl, RtlirModule* mod);
  void ElaborateItemsInOrder(const ModuleDecl* decl, RtlirModule* mod);

  void InstantiateImplicitNestedModules(
      const std::vector<std::pair<std::string_view, ModuleDecl*>>& nested,
      RtlirModule* mod);
  void ResetItemElaborationState();
  void RunPostItemValidations(const ModuleDecl* decl, RtlirModule* mod);

  void ElaborateModuleInst(ModuleItem* item, RtlirModule* mod);
  void ElaborateChildInstance(RtlirModuleInst& inst, const ModuleItem* item,
                              ModuleDecl* child_decl, RtlirModule* mod,
                              const ScopeMap& parent_scope);
  void CheckInstancePorts(RtlirModuleInst& inst, const ModuleItem* item,
                          RtlirModule* mod);

  void CheckPrimitiveTerminals(const ModuleItem* item, const RtlirModule* mod);

  void ElaborateUdpInst(ModuleItem* item, RtlirModule* mod);

  void ElaborateOneUdpInst(const ModuleItem* item, RtlirModule* mod,
                           std::optional<int64_t> index);

  UdpDecl* FindUdpByName(std::string_view name) const;
  UdpDecl* FindUdpForInstance(const ModuleItem* item);

  std::optional<UdpDecl*> ResolveUdpUseOverride(std::string_view name) const;

  void ReclassifyForwardUdpInstances(const ModuleDecl* decl);

  Expr* MakePullExpr(NetType drive);
  Expr* MakeHighZExpr();

  void BindPorts(RtlirModuleInst& inst, const ModuleItem* item,
                 RtlirModule* parent_mod, const ModuleDecl* child_decl);

  bool BindExplicitPort(const PortBindScope& scope, size_t index);
  void PrepareExplicitConnNet(const PortBindScope& scope,
                              const ExplicitPortBind& bind);
  bool ResolveExplicitTarget(const PortBindScope& scope, size_t index,
                             ExplicitPortBind& bind);
  void CheckExplicitConnLegality(const PortBindScope& scope,
                                 const ExplicitPortBind& bind);
  void RecordOutputPortDrivenVariables(const Expr* conn_expr, SourceLoc loc);
  void SynthesizeExplicitDefault(const PortBindScope& scope,
                                 ExplicitPortBind& bind);
  void CheckPortModportConsistency(const PortBindScope& scope,
                                   const RtlirPortBinding& binding,
                                   const Expr* conn_expr,
                                   const RtlirPort* child_port);
  void BindWildcardPorts(const PortBindScope& scope);
  void BindOneWildcardPort(const PortBindScope& scope, const RtlirPort& port);
  void BindWildcardDeclaredPort(const PortBindScope& scope,
                                const RtlirPort& port,
                                RtlirPortBinding& binding);
  void BindTrailingInputPorts(const PortBindScope& scope);

  void CheckPortCoercion(const RtlirModuleInst& inst, SourceLoc loc);

  void CheckUwirePortMerge(RtlirModuleInst& inst, const ModuleItem* item,
                           RtlirModule* parent_mod);

  void CheckInterconnectPortMerge(const RtlirModuleInst& inst,
                                  const ModuleItem* item,
                                  RtlirModule* parent_mod);

  void ResolveInterconnectPrimitiveTerminals(
      const std::vector<Expr*>& terminals, RtlirModule* mod);

  void ValidateUnpackedArrayPorts(const RtlirModuleInst& inst,
                                  const ModuleItem* item,
                                  RtlirModule* parent_mod);
  void ValidateInstanceArrayPorts(const RtlirModuleInst& inst,
                                  const ModuleItem* item,
                                  RtlirModule* parent_mod,
                                  const std::vector<uint32_t>& inst_dim_sizes,
                                  uint32_t total_instances);

  ScopeMap BuildParamScope(const RtlirModule* mod,
                           const std::vector<std::string_view>& scopes) const;

  ScopeMap BuildParamScope(const RtlirModule* mod) const;

  bool RefersToUnboundedParam(const RtlirModule* mod,
                              std::string_view name) const;

  bool ContainsDollarSubexpr(const Expr* e) const;

  void ElaborateGenerateIf(ModuleItem* item, RtlirModule* mod,
                           const ScopeMap& scope);

  void ElaborateGenerateCase(ModuleItem* item, RtlirModule* mod,
                             const ScopeMap& scope);

  struct ConditionalGenerateBlock {
    std::string_view name;
    bool name_is_generated = false;
    const std::vector<ModuleItem*>& body;
    bool has_begin_end = false;
  };

  void ElaborateConditionalGenerateBlock(const ConditionalGenerateBlock& block,
                                         RtlirModule* mod,
                                         const ScopeMap& scope);

  struct GenerateForOpening {
    std::string_view genvar_name;
    int64_t init_value;
  };

  std::optional<GenerateForOpening> OpenGenerateForLoop(ModuleItem* item,
                                                        RtlirModule* mod,
                                                        const ScopeMap& scope);

  void ElaborateGenerateFor(ModuleItem* item, RtlirModule* mod,
                            const ScopeMap& scope);

  void ElaborateGenerateBlockItem(ModuleItem* item, RtlirModule* mod);

  void ElaborateGenerateBlockImport(ModuleItem* item, RtlirModule* mod);

  void ElaborateGenerateItems(const std::vector<ModuleItem*>& items,
                              RtlirModule* mod, const ScopeMap& scope);

  void AssignGenerateBlockNames(const ModuleDecl* decl);

  void CheckGenerateConstructs(const ModuleDecl* decl);

  std::vector<DefparamSite> CollectDefparamSites(RtlirModule* mod,
                                                 const ModuleDecl* decl) const;

  void ApplyDefparams(RtlirModule* mod, const ModuleDecl* decl);

  void ApplyDefparamSite(RtlirModule* mod, const DefparamSite& site,
                         const ScopeMap& scope);

  void ApplyDefparamsRecursively(RtlirModule* mod);

  struct DefparamTopRooted {
    RtlirModule* root;
    HierPath steps;
    RtlirModule* target_mod;
  };
  RtlirParamDecl* ResolveDefparamFromTop(const HierPath& path,
                                         DefparamTopRooted& rooted);

  void WarnUnresolvedDefparams(RtlirModule* mod);
  void ReportUnresolvedDefparams(RtlirModule* mod, const ModuleDecl* decl);

  void ReportUnresolvedDefparamSite(RtlirModule* mod, const DefparamSite& site,
                                    const ScopeMap& mod_scope);
  const RtlirParamDecl* ParamWithStepsAfterIt(RtlirModule* mod,
                                              const HierPath& path);
  bool ReportUnappliedDefparamPath(RtlirModule* mod, SourceLoc loc,
                                   const HierPath& path);

  void CheckEarlyResolutionAmbiguity(
      RtlirModule* mod, const std::unordered_set<std::string_view>& top_names);

  void ProcessPendingGenerate(const PendingGenerate& pg);

  RtlirParamDecl* ResolveDefparamSteps(RtlirModule* root, const HierPath& path,
                                       const HierPath& writer,
                                       RtlirModule** out_mod = nullptr);

  void RecomputeDependentParams(RtlirModule* mod);
  void RefoldChildOverrides(RtlirModule* mod, const ScopeMap& mod_scope);
  bool MaybeCreateImplicitNet(std::string_view name, SourceLoc loc,
                              RtlirModule* mod);
  bool DeclaresNetOrVariable(std::string_view name) const;
  bool NamesNet(std::string_view name, SourceLoc loc) const;
  std::unordered_set<std::string_view> NetNamesAt(SourceLoc loc) const;
  void DeclareInModuleNameSpace(std::string_view name, SourceLoc loc);

  std::string_view ScopedName(std::string_view base);
  std::string_view InternedGenPrefix();
  std::string_view ResolveTypeRef(DataType& dt, SourceLoc loc,
                                  const RtlirModule* mod);

  void ValidateArrayInitPattern(const ModuleItem* item);
  void ValidateStructInitPattern(const ModuleItem* item);

  void ValidateModuleConstraints(const ModuleDecl* decl, RtlirModule* mod);

  void ValidateTimescaleConsistency();

  void ValidateTimescaleOrder();

  void ValidateEnumDecl(const DataType& dtype, SourceLoc loc,
                        bool declares_its_constants);

  void ValidateVirtualInterfaceContAssign(const ModuleItem* item);

  void ValidateVirtualInterfaceSensitivity(const ModuleItem* item);
  void ReportVirtualInterfaceInInferredSensitivity(const ModuleItem* item);

  void ValidateVirtualInterfaceOps(const ModuleDecl* decl);

  void WalkStmtsForVirtualInterfaceOps(const Stmt* s);

  void ValidateEventOps(const ModuleDecl* decl);

  void ValidateGetpatternUses(const ModuleDecl* decl);
  void ValidateGetpatternContAssign(const ModuleItem* item,
                                    const RtlirModule* mod);
  bool NamesMemoryElement(const Expr* arg) const;

  void WalkStmtsForEventOps(const Stmt* s);

  void ValidateVirtualInterfaceClocking(const ModuleDecl* decl);

  void WalkStmtsForVirtualInterfaceClocking(const Stmt* s);

 public:
  void ValidateArrayOfVifInitStmt(const Stmt* s);

 private:
  void ValidateInterfaceObjectAccess(const ModuleDecl* decl);
  void ValidateGenericPortModportAccess(const ModuleDecl* child,
                                        const RtlirModuleInst& inst);

  void ValidatePackedDimRange(const DataType& dtype, SourceLoc loc);

  void ValidateUnpackedDimRange(const std::vector<Expr*>& dims, SourceLoc loc);

  void ValidatePackedDimOnPredefinedType(const DataType& dtype, SourceLoc loc);

  void ValidatePackedDimOnDisallowedType(const DataType& dtype, SourceLoc loc);

  void ValidateArrayAssignments(const ModuleDecl* decl);

  void ValidateAssocArraySlices(const ModuleDecl* decl);

  void ValidateAssocWildcardTraversal(const ModuleDecl* decl);
  void ValidateAssocTraversalArgType(const ModuleDecl* decl);

  void ValidateArrayOrderingMethods(const ModuleDecl* decl);

  void ValidateClassIndexSelect(const ModuleDecl* decl);

  void ValidateStringIndexSelect(const ModuleDecl* decl);

  void ValidateIntegralIndexSelect(const ModuleDecl* decl);

  void TrackVarArrayInfo(
      const ModuleItem* item, RtlirVariable& var, const ScopeMap& scope,
      std::unordered_map<std::string_view, VarArrayInfo>& out);
  void RecordNetArrayShape(ModuleItem* item, const RtlirNet& net,
                           RtlirModule* mod);

  void ValidateVarDeclTypes(ModuleItem* item, const ScopeMap& scope,
                            bool writes_its_type);

  bool ValidateEnumLiteral(const EnumMember& member, uint32_t base_width,
                           bool is_2state);

  void ValidateEdgeOnReal(const ModuleItem* item);
  void ValidateItemConstraints(const ModuleItem* item, const RtlirModule& mod,
                               const ScopeMap& scope);
  void ValidateItemRules(const ModuleItem* item, const RtlirModule& mod,
                         const ScopeMap& scope);

  void ValidateDeferredAssertionActions(const ModuleDecl* decl);
  void WalkStmtsForDeferredActions(
      const Stmt* s, const std::unordered_set<std::string_view>& auto_vars);

  void ValidateChandleContAssign(const ModuleItem* item);

  void ValidateChandleSensitivity(const ModuleItem* item);

  void ValidateChandleOps(const ModuleDecl* decl);
  void WalkStmtsForChandleOps(const Stmt* s);

  void ValidateInterconnectContAssign(const ModuleItem* item);

  void ValidateMixedAssignments();

  void ValidateInputPortAssignments(const ModuleDecl* decl);

  void ValidatePatterns(const ModuleDecl* decl);

  void ValidateProceduralNetAssign();
  void ValidateDynamicArrayNba(const ModuleDecl* decl);
  void AdoptProceduralTypedefDims(const ModuleDecl* decl);
  void AdoptTypedefDimsInStmt(Stmt* s);
  void ValidateArrayQueryOnDynamicType(const ModuleDecl* decl);
  void ValidateArrayQueryOnVariableDim(const ModuleDecl* decl);
  void ValidateRandomSeedType(const ModuleDecl* decl);
  void ValidatePlaOutputTerms(const ModuleDecl* decl);
  void ValidateStringOutputTaskTargets(const ModuleDecl* decl);
  void ValidatePlaAscendingOrder(const ModuleDecl* decl);
  void ValidateBitsCallRestrictions(const ModuleDecl* decl);
  void ValidateBitVectorFunctionArgs(const ModuleDecl* decl);

  void ValidatePartSelectBounds(const ModuleDecl* decl);

  void ValidateElabSystemTask(const ModuleItem* item, const RtlirModule* mod);

  void ElaborateLetFormals(ModuleItem* item, const RtlirModule* mod);

  void ValidateDpiImport(const ModuleItem* item);

  void ValidateDpiDeclarations();

  void ValidateDpiGlobalNameSpace();

  void ValidateTypenameAsElabConstant(const Expr* init);

  void ValidateAlias(const ModuleItem* item, RtlirModule* mod);

  void ValidateSpecparamInParams(const ModuleDecl* decl);

  void ValidateSpecparamInDeclRange(const ModuleDecl* decl);

  void ValidateValueParams(const ModuleDecl* decl, const RtlirModule* mod);

  void ValidateLhsPatternWidths(const ModuleDecl* decl, const RtlirModule* mod);

  void CheckAlwaysCombMultiDriver(const ModuleDecl* decl, RtlirModule* mod);

  void CheckAggregateElementDrivers(const ModuleDecl* decl, RtlirModule* mod);

  void ValidateDisableTargets(const ModuleDecl* decl);

  void ValidateFinalTaskEnables(const ModuleDecl* decl);

  void ValidateFunctionBody(const ModuleItem* item,
                            bool is_class_method = false);

  void ValidateFunctionArgDefaultsScope(const ModuleItem* item);

  void ValidateAutomaticVarProcWrites(const ModuleDecl* decl);

  void ValidateJumpStatements(const ModuleDecl* decl);

  void ValidateForeachLoops(const ModuleDecl* decl);

  void ValidateRandsequenceProductionNames(const ModuleDecl* decl);

  void CheckJumpStatementsIn(const std::vector<ModuleItem*>& items);
  void CheckForeachLoopsIn(const std::vector<ModuleItem*>& items);
  void CheckForeachLoopsInClass(const ClassDecl* cls);
  void CheckPatternsIn(const std::vector<ModuleItem*>& items);
  void CheckPatternsInClass(const ClassDecl* cls);
  void CheckRandsequenceNamesIn(const std::vector<ModuleItem*>& items);

  void ValidatePerDeclarationRulesInUnitScopes();

  void ValidateConstantFunctionCalls(const ModuleDecl* decl);
  void ValidateTaskCallsInExpressions(const ModuleDecl* decl);
  std::unordered_set<std::string> ReachableTaskNames() const;
  void ValidateDpiOpenArrayArgs(const ModuleDecl* decl);
  void WalkStmtsForDpiArgs(const Stmt* s);
  void WalkExprForDpiCalls(const Expr* e);
  void CheckDpiOpenArrayCall(const Expr* call);

  void ValidateBackgroundFuncCallContext(const ModuleDecl* decl);

  void ValidateSubroutineCallArgs(const ModuleDecl* decl);
  void ValidateRefArgActuals(const ModuleDecl* decl);
  void ResetPendingElaboration();

  void ValidateScopeRandomizeCalls(const ModuleDecl* decl);

  void ValidateParameterizedMailboxCalls(const ModuleDecl* decl);

  void ValidateStdClassMethodCalls(const ModuleDecl* decl);

  void ValidateArrayArgTypes(const ModuleDecl* decl);

  void TrackEnumVariable(const ModuleItem* item);
  void EmitBareEnumMembers(const ModuleItem* item, RtlirModule* mod);

  void ValidateEnumAssignments(const ModuleDecl* decl);

  void WalkStmtsForEnumAssign(const Stmt* s);

  void ValidateConstAssignments(const ModuleDecl* decl);

  void ValidateUnitConstAssignments();

  void CheckEnumAssignStmt(const Stmt* s);

  void WalkExprForEnumCalls(const Expr* e);
  void CheckEnumCallArguments(const Expr* call);

  void ValidateClassMethodBodies(const ModuleDecl* decl);

  void DefaultPackageTaskFuncLifetimes();
  void ValidatePackageValueParams();

  void ValidateSequenceEventArgs(const ModuleDecl* decl, RtlirModule* mod);

  void ValidateClockingBlock(ModuleItem* item, const RtlirModule* mod);

  void ValidateNoFormalShadowedByBodyLocal(ModuleItem* item);

  void ValidateRecursiveProperty(const ModuleItem* item);
  void ValidateRecursivePropertyArguments(const ModuleItem* item);

  void ValidateClockvarAccess(const ModuleDecl* decl);
  void ValidateCycleDelayDefaultClocking(const ModuleDecl* decl);
  void ValidateIntraAssignCycleDelay(const ModuleDecl* decl);
  void ValidateDuplicateDefaultClocking(const ModuleDecl* decl);
  void ValidateDefaultClockingReference(const ModuleDecl* decl);
  void ValidateDuplicateGlobalClocking(const ModuleDecl* decl);
  void ValidateDuplicateDefaultDisableIff(const ModuleDecl* decl);
  void ValidateGlobalClockReference(const ModuleDecl* decl);
  void ValidateGclkRequiresGlobalClocking(const ModuleDecl* decl);
  void ValidateFutureGclkPlacement(const ModuleDecl* decl);
  void ValidateContAssignToClockvar(const ModuleDecl* decl);
  void WalkStmtsForClockvarAccess(const Stmt* s);
  void CheckClockvarAccessExpr(const Expr* e, bool is_lvalue);
  void ValidateSyncDriveForm(const ModuleDecl* decl);
  void ValidateClockingSignalTargets(const ModuleDecl* decl);
  bool ExprTargetsWritableClockvar(const Expr* e) const;

  bool IsOutputClockvarSignal(std::string_view name) const;
  void ValidatePrimitiveDriveToClockvar(const ModuleDecl* decl);

  void ValidateScopeRules(const ModuleDecl* decl);

  void ValidateUnresolvedReferences(const ModuleDecl* decl,
                                    const RtlirModule* mod);
  bool IsDeclaredNameForRhs(std::string_view name) const;
  bool IsNameInModuleScope(std::string_view name) const;
  bool IsNameInEnclosingScope(std::string_view name) const;

  std::unordered_set<std::string_view> CaptureCurrentScopeNames() const;

  void ValidateHierRefIntoChecker(const ModuleDecl* decl);
  void ValidateFreeCheckerVariableAssignments(const ModuleDecl* decl);
  void ValidateCheckerVariableInitialAssignment(const ModuleDecl* decl);
  void ValidateHierRefInstanceArray(const ModuleDecl* decl,
                                    const RtlirModule* mod);
  void CheckHierRefUndeclaredMember(
      const std::unordered_map<std::string_view, const RtlirModule*>& inst_type,
      const Expr* ma);
  void ValidateHierRefToAutomatic(const ModuleDecl* decl);
  void ValidateHierRefIntoProgram(const ModuleDecl* decl);

  void ValidateProgramSubroutineCall(const ModuleDecl* decl);

  void ValidateProgramWideSpaceAccess(const ModuleDecl* decl);

  void ValidateProgramWideSpaceAccessInPackageAndCuScopes();

  void ApplyBindDirectives(const std::vector<RtlirModule*>& tops);
  struct BindWalkCtx;
  void WalkForBind(RtlirModule* mod, const std::string& hier_path,
                   bool under_bind, BindWalkCtx& ctx);
  void ApplyBindInstance(BindDirective* bd, RtlirModule* target);

  void ValidateModportExportConflicts(RtlirModule* top);
  void WalkForExportConflicts(RtlirModule* mod,
                              std::unordered_set<RtlirModule*>& visited);

  void ApplyConfigParamOverrides(const ModuleItem* item,
                                 const ModuleDecl* child_decl,
                                 ParamList& child_params,
                                 const ScopeMap& parent_scope,
                                 std::vector<std::string_view>& locked);
};

}  // namespace delta
