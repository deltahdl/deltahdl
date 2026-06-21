#pragma once

#include <cstdint>
#include <optional>
#include <set>
#include <string>
#include <string_view>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

class Arena;
class DiagEngine;
struct RtlirDesign;
struct RtlirModule;
struct RtlirVariable;
struct RtlirModuleInst;
struct RtlirParamDecl;

class Elaborator {
 public:
  using ParamList = std::vector<std::pair<std::string_view, int64_t>>;

  Elaborator(Arena& arena, DiagEngine& diag, CompilationUnit* unit);

  RtlirDesign* Elaborate(std::string_view top_module_name);

  RtlirDesign* Elaborate(const ConfigDecl* cfg);

  void SetLibraryDeclarationOrder(std::vector<std::string> order);

 private:
  void RunPreElaborationValidations();

  RtlirDesign* ElaborateTops(const std::vector<ModuleDecl*>& top_decls);
  // Elaborates each top-level module declaration into `design`; returns false
  // (after reporting) if any top fails to elaborate.
  bool ElaborateTopModules(const std::vector<ModuleDecl*>& top_decls,
                           RtlirDesign* design);
  // §23.10.4 / §27: runs the defparam-application and pending-generate
  // expansion fixpoint over every top in `design` until no generates remain.
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

  void ValidateAnonymousProgramNameSharing();

  void ValidateAnonymousProgramHierRefs();

  void ValidatePackageItems();

  void ValidatePackageReferences();

  void ValidatePackageExports();

  void ValidatePackageImportRules(const ModuleDecl* decl);

  void ValidateHierRefToImportedName(const ModuleDecl* decl,
                                     const RtlirModule* mod);

  void ApplyHeaderImports(const ModuleDecl* decl);

  void ValidateModports();

  void ValidateSpecifyBlocks();

  void RegisterCuScopeItems();

  void ResolveExternModules();

  ModuleDecl* FindModule(std::string_view name) const;

  // Applies a cell selection clause's use expansion to a cell being resolved
  // (§33.4.1.4, §33.4.1.6). Returns nullopt when no clause applies (resolution
  // should continue normally); a present value (possibly nullptr) is the bound
  // cell, where nullptr means the named target does not exist.
  std::optional<ModuleDecl*> ResolveCellUseOverride(
      std::string_view name) const;

  ModuleDecl* FindModuleInScope(std::string_view name) const;

  RtlirModule* ElaborateModule(const ModuleDecl* decl, const ParamList& params);

  void ElaboratePorts(const ModuleDecl* decl, RtlirModule* mod);

  static bool HasParamPortWithoutDefault(const ModuleDecl* decl);

  void ElaborateItem(ModuleItem* item, RtlirModule* mod);
  // Two-level dispatch for ElaborateItem: each handles a cohesive subset of
  // module-item kinds and returns true when it consumed `item->kind`.
  bool ElaborateDeclItem(ModuleItem* item, RtlirModule* mod);
  bool ElaborateBehavioralItem(ModuleItem* item, RtlirModule* mod);
  // Third-level dispatch for the §16 assertion/sequence/property/clocking
  // module items; returns true for those kinds and is a no-op (true) otherwise.
  bool ElaborateAssertionItem(ModuleItem* item, RtlirModule* mod);
  void ElaborateParamDecl(ModuleItem* item, RtlirModule* mod);
  void ElaborateNetDecl(ModuleItem* item, RtlirModule* mod);
  void ElaborateVarDecl(ModuleItem* item, RtlirModule* mod);
  // §23.2.2.1: reconciles the signedness of a non-ANSI port with its separate
  // net or variable declaration -- `signed` on either side makes both signed.
  // Returns the reconciled signedness for the net/variable declaration.
  bool ReconcilePartialPortSignedness(std::string_view name, bool decl_signed,
                                      RtlirModule* mod);
  void SetStructTypeInfo(const ModuleItem* item, RtlirVariable& var);
  void ElaborateContAssign(ModuleItem* item, RtlirModule* mod);
  void ValidateContAssignIdentLhs(ModuleItem* item, RtlirModule* mod);
  void ValidateContAssignNettypeAndDelay(ModuleItem* item);
  void ValidateContAssignDriveStrength(ModuleItem* item, RtlirModule* mod);
  void ElaborateSpecparam(ModuleItem* item, RtlirModule* mod);

  void ElaborateTypedef(ModuleItem* item, RtlirModule* mod);

  void ElaborateNettypeDecl(ModuleItem* item, RtlirModule* mod);

  void ElaborateItems(const ModuleDecl* decl, RtlirModule* mod);
  // Clears every per-module bookkeeping table before a module's items are
  // elaborated, and runs the post-item legality validations for `decl`/`mod`.
  void ResetItemElaborationState();
  void RunPostItemValidations(const ModuleDecl* decl, RtlirModule* mod);

  void ElaborateModuleInst(ModuleItem* item, RtlirModule* mod);

  UdpDecl* FindUdpByName(std::string_view name) const;

  void ReclassifyForwardUdpInstances(const ModuleDecl* decl);

  Expr* MakePullExpr(NetType drive);
  Expr* MakeHighZExpr();

  void BindPorts(RtlirModuleInst& inst, const ModuleItem* item,
                 RtlirModule* parent_mod);

  // §23.3.3 per-instance binding scope shared by the BindPorts helpers.
  struct PortBindScope {
    RtlirModuleInst& inst;
    const ModuleItem* item;
    RtlirModule* parent_mod;
    bool has_pull;
    bool is_ordered;
  };
  // Mutable per-connection state threaded through the BindExplicitPort helpers.
  struct ExplicitPortBind {
    RtlirPortBinding& binding;
    const Expr* conn_expr;
    std::string_view port_name;
    const RtlirPort* child_port;  // nullptr when no port matches
    bool is_implicit;
  };
  // Binds the explicit port connection at `index`; returns false to stop the
  // loop (too many ordered connections for the instantiated module).
  bool BindExplicitPort(const PortBindScope& scope, size_t index);
  // Declares an implicit net (named form) or diagnoses an undeclared signal.
  void PrepareExplicitConnNet(const PortBindScope& scope,
                              const ExplicitPortBind& bind);
  // Resolves the targeted child port, fills the binding direction/width, and
  // runs named-connection net-type checks. Returns false to stop the loop.
  bool ResolveExplicitTarget(const PortBindScope& scope, size_t index,
                             ExplicitPortBind& bind);
  // Connection-legality checks: assignment compatibility, replication,
  // assignment-pattern, and multiple-driver rules.
  void CheckExplicitConnLegality(const PortBindScope& scope,
                                 const ExplicitPortBind& bind);
  // Synthesizes a connection for an unconnected input port
  // (default/pull/highZ).
  void SynthesizeExplicitDefault(const PortBindScope& scope,
                                 ExplicitPortBind& bind);
  // §25.5 header-vs-connection modport consistency for an interface port.
  void CheckPortModportConsistency(const PortBindScope& scope,
                                   const RtlirPortBinding& binding,
                                   const Expr* conn_expr,
                                   const RtlirPort* child_port);
  // §23.3.2.2 wildcard `.*` completion: binds each not-yet-connected port.
  void BindWildcardPorts(const PortBindScope& scope);
  void BindOneWildcardPort(const PortBindScope& scope, const RtlirPort& port);
  // Wildcard completion when a same-named signal is declared in the scope.
  void BindWildcardDeclaredPort(const PortBindScope& scope,
                                const RtlirPort& port,
                                RtlirPortBinding& binding);
  // Trailing unconnected-input completion when no wildcard appears.
  void BindTrailingInputPorts(const PortBindScope& scope);

  void CheckPortCoercion(const RtlirModuleInst& inst, SourceLoc loc);

  void CheckUwirePortMerge(const RtlirModuleInst& inst, const ModuleItem* item,
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

  ScopeMap BuildParamScope(const RtlirModule* mod) const;

  // §6.20.7: returns true if `name` matches an already-elaborated parameter of
  // `mod` that was assigned $ (an unbounded parameter).
  bool RefersToUnboundedParam(const RtlirModule* mod,
                              std::string_view name) const;

  // §6.20.7: returns true if a literal $ appears anywhere inside `e`. Used to
  // reject parameter values where $ is combined with operators or selects
  // instead of standing alone as the entire (self-contained) expression.
  bool ContainsDollarSubexpr(const Expr* e) const;

  void ElaborateGenerateIf(ModuleItem* item, RtlirModule* mod,
                           const ScopeMap& scope);

  void ElaborateGenerateCase(ModuleItem* item, RtlirModule* mod,
                             const ScopeMap& scope);

  void ElaborateGenerateFor(ModuleItem* item, RtlirModule* mod,
                            const ScopeMap& scope);

  void ElaborateGenerateItems(const std::vector<ModuleItem*>& items,
                              RtlirModule* mod, const ScopeMap& scope);

  void AssignGenerateBlockNames(const ModuleDecl* decl);

  void CheckConditionalGenerateNaming(const ModuleDecl* decl);

  void ApplyDefparams(RtlirModule* mod, const ModuleDecl* decl);

  void ApplyDefparamsRecursively(RtlirModule* mod);

  void WarnUnresolvedDefparams(RtlirModule* mod);

  void VerifyEarlyResolvedDefparams();

  void CheckEarlyResolutionAmbiguity(
      RtlirModule* mod, const std::unordered_set<std::string_view>& top_names);

  void ProcessPendingGenerate(ModuleItem* item, RtlirModule* mod);

  RtlirParamDecl* ResolveDefparamPath(RtlirModule* root, const Expr* path_expr,
                                      RtlirModule** out_mod = nullptr);

  void RecomputeDependentParams(RtlirModule* mod);

  bool MaybeCreateImplicitNet(std::string_view name, SourceLoc loc,
                              RtlirModule* mod);

  std::string_view ScopedName(std::string_view base);

  void ResolveTypeRef(ModuleItem* item, const RtlirModule* mod);

  bool ResolveParameterizedType(DataType& dtype);

  void ValidateArrayInitPattern(const ModuleItem* item);
  void ValidateStructInitPattern(const ModuleItem* item);

  void ValidateModuleConstraints(const ModuleDecl* decl);

  void ValidateTimescaleConsistency();

  void ValidateEnumDecl(const DataType& dtype, SourceLoc loc);

  void ValidatePackedStructDefaults(const DataType& dtype, SourceLoc loc);

  void ValidateUnpackedStructWithUnionDefaults(const DataType& dtype,
                                               SourceLoc loc);

  void ValidateStructMemberDefaultsConstant(const DataType& dtype,
                                            SourceLoc loc);

  void ValidateVoidMembers(const DataType& dtype, SourceLoc loc);

  void ValidateRandQualifiers(const DataType& dtype, SourceLoc loc);

  void ValidatePackedDimRequiresPackedKeyword(const DataType& dtype,
                                              SourceLoc loc);

  void ValidatePackedStructMemberTypes(const DataType& dtype, SourceLoc loc);

  void ValidateChandleInUnion(const DataType& dtype, SourceLoc loc);

  void ValidateVirtualInterfaceInUnion(const DataType& dtype, SourceLoc loc);

  void ValidateVirtualInterfaceContAssign(const ModuleItem* item);

  void ValidateVirtualInterfaceSensitivity(const ModuleItem* item);

  void ValidateVirtualInterfaceOps(const ModuleDecl* decl);

  void WalkStmtsForVirtualInterfaceOps(const Stmt* s);

  // §15.5.5.3: restrict the operators allowed on event variables.
  void ValidateEventOps(const ModuleDecl* decl);

  void WalkStmtsForEventOps(const Stmt* s);

  void ValidateVirtualInterfaceClocking(const ModuleDecl* decl);

  void WalkStmtsForVirtualInterfaceClocking(const Stmt* s);

  // Public so the free recursive walker in elaborator_validate_interface.cpp
  // can drive it over a statement tree.
 public:
  void ValidateArrayOfVifInitStmt(const Stmt* s);

 private:
  void ValidateInterfaceObjectAccess(const ModuleDecl* decl);

  void ValidatePackedUnion(const DataType& dtype, SourceLoc loc);

  void ValidatePackedDimRange(const DataType& dtype, SourceLoc loc);

  void ValidateUnpackedDimRange(const std::vector<Expr*>& dims, SourceLoc loc);

  void ValidatePackedDimOnPredefinedType(const DataType& dtype, SourceLoc loc);

  void ValidatePackedDimOnDisallowedType(const DataType& dtype, SourceLoc loc);

  void ValidateArrayAssignments(const ModuleDecl* decl);
  void ValidateOneArrayAssignment(const ModuleItem* item);
  void CheckArrayAssignExprs(const Expr* lhs, const Expr* rhs, SourceLoc loc);
  void WalkStmtsForArrayAssign(const Stmt* s);

  void ValidateAssocArraySlices(const ModuleDecl* decl);

  void ValidateAssocWildcardTraversal(const ModuleDecl* decl);
  void ValidateAssocTraversalArgType(const ModuleDecl* decl);

  void ValidateArrayOrderingMethods(const ModuleDecl* decl);

  void ValidateClassIndexSelect(const ModuleDecl* decl);

  void ValidateStringIndexSelect(const ModuleDecl* decl);

  void ValidateIntegralIndexSelect(const ModuleDecl* decl);

  void ValidateAssocIndexType(const ModuleItem* item);

  void TrackVarArrayInfo(const ModuleItem* item, const RtlirVariable& var);

  void ValidateVarDeclTypes(ModuleItem* item);

  bool ValidateEnumLiteral(const EnumMember& member, uint32_t base_width,
                           bool is_2state);

  void ValidateEdgeOnReal(const ModuleItem* item);

  void ValidateItemConstraints(const ModuleItem* item);

  void ValidateDeferredAssertionActions(const ModuleDecl* decl);
  void WalkStmtsForDeferredActions(const Stmt* s);
  std::unordered_map<std::string_view, const ModuleItem*>
      deferred_subroutine_map_;

  void ValidateChandleContAssign(const ModuleItem* item);

  void ValidateChandleSensitivity(const ModuleItem* item);

  void ValidateChandleOps(const ModuleDecl* decl);
  void WalkStmtsForChandleOps(const Stmt* s);

  void ValidateInterconnectContAssign(const ModuleItem* item);

  void ValidateMixedAssignments();

  // §23.3.3.2: a variable declared as an input port is already driven by the
  // implied continuous assignment from its port connection, so an additional
  // continuous or procedural assignment to it inside the module is illegal.
  void ValidateInputPortAssignments(const ModuleDecl* decl);

  // §12.6: a constant expression pattern shall be of integral type.
  void ValidateMatchesPatternIntegral(const ModuleDecl* decl);

  // §12.6.1: the tested expression of a pattern-matching case statement shall
  // have a known type that is the same as the type of the pattern in each item.
  void ValidateMatchesCaseSelectorType(const ModuleDecl* decl);

  // §12.6.2: in each `e matches p` clause of an if-else predicate, e and p
  // shall have the same statically known type.
  void ValidateMatchesIfPredicateType(const ModuleDecl* decl);

  void ValidateProceduralNetAssign();
  void ValidateDynamicArrayNba(const ModuleDecl* decl);
  void ValidateArrayQueryOnDynamicType(const ModuleDecl* decl);
  void ValidateArrayQueryOnVariableDim(const ModuleDecl* decl);
  void ValidateRandomSeedType(const ModuleDecl* decl);
  void ValidatePlaOutputTerms(const ModuleDecl* decl);
  void ValidatePlaAscendingOrder(const ModuleDecl* decl);
  void ValidateBitsCallRestrictions(const ModuleDecl* decl);

  void ValidateContAssignConstSelect(const ModuleDecl* decl);
  void ValidatePartSelectBounds(const ModuleDecl* decl);

  void ValidateElabSystemTask(const ModuleItem* item, const RtlirModule* mod);

  // §11.12: a typed let formal argument shall be `event` or one of the types
  // allowed in §16.6.
  void ValidateLetDecl(const ModuleItem* item);

  // §35.5.2: pure-only restrictions on imported subroutines.
  void ValidateDpiImport(const ModuleItem* item);

  // §35.5.4: duplicate import-name detection per declaration scope and
  // type-signature consistency across all declarations that share a single
  // linkage name (c_identifier, defaulting to the SystemVerilog name).
  void ValidateDpiDeclarations();

  // §35.4: per-scope uniqueness for export declarations and global agreement
  // on the DPI version string across every declaration that shares a single
  // linkage identifier.
  void ValidateDpiGlobalNameSpace();

  void ValidateTypenameAsElabConstant(const Expr* init);

  void ValidateAlias(const ModuleItem* item, RtlirModule* mod);

  void ValidateSpecparamInParams(const ModuleDecl* decl);

  void ValidateSpecparamInDeclRange(const ModuleDecl* decl);

  void ValidateValueParams(const ModuleDecl* decl, const RtlirModule* mod);

  void ValidateLhsPatternWidths(const ModuleDecl* decl, const RtlirModule* mod);

  void CheckAlwaysCombMultiDriver(const ModuleDecl* decl, RtlirModule* mod);

  void ValidateDisableTargets(const ModuleDecl* decl);

  void ValidateFunctionBody(const ModuleItem* item);

  void ValidateFunctionArgDefaultsScope(const ModuleItem* item);

  void ValidateAutomaticVarProcWrites(const ModuleDecl* decl);

  // §12.8 — break/continue must be inside a loop and may not target a loop
  // outside their enclosing fork-join; return must be inside a subroutine and
  // a value-returning function shall return an expression.
  void ValidateJumpStatements(const ModuleDecl* decl);

  // §12.7.3 — foreach loop variables may not outnumber the array's
  // dimensions, are read-only, and may not reuse the array's identifier.
  void ValidateForeachLoops(const ModuleDecl* decl);

  void ValidateConstantFunctionCalls(const ModuleDecl* decl);

  // §7.7: a dynamic array or queue may not be passed to a DPI import formal
  // that is an open array (unsized) with an output direction.
  void ValidateDpiOpenArrayArgs(const ModuleDecl* decl);
  void WalkStmtsForDpiArgs(const Stmt* s);
  void WalkExprForDpiCalls(const Expr* e);
  void CheckDpiOpenArrayCall(const Expr* call);

  // §13.4.4
  void ValidateBackgroundFuncCallContext(const ModuleDecl* decl);

  void ValidateSubroutineCallArgs(const ModuleDecl* decl);

  void ValidateArrayArgTypes(const ModuleDecl* decl);

  void TrackEnumVariable(const ModuleItem* item);

  void ValidateEnumAssignments(const ModuleDecl* decl);

  void WalkStmtsForEnumAssign(const Stmt* s);

  void ValidateConstAssignments(const ModuleDecl* decl);

  void WalkStmtsForConstAssign(const Stmt* s);

  void CheckEnumAssignStmt(const Stmt* s);

  // §6.19.3: strong typing also applies when an actual argument is bound to an
  // enum-typed formal of a called subroutine.
  void WalkExprForEnumCalls(const Expr* e);
  void CheckEnumCallArguments(const Expr* call);

  void ValidateClassHandleOps(const ModuleDecl* decl);

  void WalkStmtsForClassHandleOps(const Stmt* s);

  void ValidateClassHandleContAssign(const ModuleItem* item);

  void ValidateStaticMethodBodies(const ModuleDecl* decl);
  void ValidateOneClassStaticMethods(const ClassDecl* cls);

  void ValidateThisUsage(const ModuleDecl* decl);
  void ValidateThisInItem(const ModuleItem* item);

  void ValidateFinalClassExtension();

  void ValidateWeakReferenceMembers();

  void ValidateClassMethodBodies(const ModuleDecl* decl);

  void ApplyClassMethodAutomaticDefault();

  void ValidateChainingConstructors();
  void ValidateOneClassChainingCtor(const ClassDecl* cls);
  void ValidateOneClassDefaultKeyword(const ClassDecl* cls);

  void ValidateEmbeddedCovergroupAssign();
  void ValidateDerivedCovergroupBase();

  void ValidateLocalProtectedAccess(const ModuleDecl* decl);

  void ValidateConstClassProperties();

  void ValidateVirtualMethodOverrides();
  void ValidateOneMethodOverride(const ClassDecl* cls, const ClassMember* m);

  void ValidateAbstractClassRules();
  void ValidateAbstractClassUnimplemented(const ClassDecl* cls);
  void ValidateSuperInNonDerivedClass();

  void ValidateOutOfBlockDeclarations();

  void ValidateParameterizedScopeResolution(const ModuleDecl* decl);

  // §6.20.3 / §8.23: a type parameter may prefix the class scope resolution
  // operator only in a typedef declaration, the type operator, or a type
  // parameter assignment, never in an ordinary expression.
  void ValidateTypeParamScopeUsage(const ModuleDecl* decl);

  // §6.20.3: a type parameter used as a class scope resolution prefix shall
  // resolve to a class.
  void ValidateTypeParamScopePrefixResolvesToClass(const ModuleDecl* decl);

  void ValidateInterfaceClassRules();

  void ValidateForwardClassTypedefs();

  // 18.4: random variable type rules for rand/randc class properties.
  void ValidateRandomVariableTypes();
  void ValidateOneClassRandomVariables(const ClassDecl* cls);

  // 18.5: constraint block names shall be unique within a class.
  void ValidateConstraintBlockNames();
  void ValidateOneClassConstraintNames(const ClassDecl* cls);

  // 18.5.7.1: in a foreach iterative constraint the number of loop variables
  // shall not exceed the number of dimensions of the iterated array.
  void ValidateForeachConstraintDims();
  void ValidateOneClassForeachConstraintDims(const ClassDecl* cls);

  // 18.5.9: a solve...before ordering constraint may name only rand variables
  // (never randc), each integral or real, with no circular dependency.
  void ValidateSolveBeforeConstraints();
  void ValidateOneClassSolveBeforeConstraints(const ClassDecl* cls);
  bool IsSolveOrderableType(const DataType& dt) const;

  // 18.5.13.1: a soft constraint may be specified only on a random variable;
  // it may not be specified for a randc variable.
  void ValidateSoftConstraintVariables();
  void ValidateOneClassSoftConstraintVariables(const ClassDecl* cls);

  // 18.5.11: a function called from a constraint expression shall not have
  // output, inout, or non-const ref arguments (const ref is allowed).
  void ValidateConstraintFunctionArgs();
  void ValidateOneClassConstraintFunctionArgs(const ClassDecl* cls);

  // 18.8: rand_mode() is a built-in method and cannot be overridden, so a
  // class shall not declare a method of that name.
  void ValidateBuiltinRandomizationMethods();
  void ValidateOneClassBuiltinMethods(const ClassDecl* cls);

  // 18.5.1: external constraint blocks complete constraint prototypes.
  void ValidateExternalConstraints();
  void ValidateOneClassExternalConstraints(const ClassDecl* cls);

  // 18.5.2: constraint inheritance and override specifiers.
  void ValidateConstraintInheritance();
  void ValidateOneConstraintOverride(const ClassDecl* cls,
                                     const ClassMember* m);
  void ValidateNonAbstractPureConstraints(const ClassDecl* cls);
  void ValidateConstraintSpecifierParity(const ClassDecl* cls,
                                         const ClassMember* m);

  void ValidateForwardTypedefsInScope(const ModuleDecl* decl);

  void ValidateForwardTypedefScopePrefix(const ModuleDecl* decl);
  void ValidateInterfaceClassMembers(const ClassDecl* cls);
  void ValidateInterfaceClassInheritance(const ClassDecl* cls);
  void ValidateRegularClassInheritance(const ClassDecl* cls);
  void ValidateImplementsInterfaceMethods(const ClassDecl* cls);

  void ValidateSequenceEventArgs(const ModuleDecl* decl);

  void ValidateClockingBlock(ModuleItem* item, const RtlirModule* mod);

  // §16.10: a formal-argument name of a sequence/property declaration cannot
  // also be declared as a body-scope local variable in an
  // assertion_variable_declaration. Diagnoses the redeclaration on `item`.
  void ValidateNoFormalShadowedByBodyLocal(ModuleItem* item);

  // §16.12.17 / §F.7: enforce the four restrictions on recursive property
  // declarations against `item` (a property declaration).
  void ValidateRecursiveProperty(const ModuleItem* item);
  // §16.12.17 Restriction 4 / §F.7 RESTRICTION 4: the actual-argument rule on
  // recursive instances appearing in the body of `item`.
  void ValidateRecursivePropertyArguments(const ModuleItem* item);

  void ValidateClockvarAccess(const ModuleDecl* decl);
  void ValidateCycleDelayDefaultClocking(const ModuleDecl* decl);
  void ValidateIntraAssignCycleDelay(const ModuleDecl* decl);
  void ValidateDuplicateDefaultClocking(const ModuleDecl* decl);
  void ValidateDefaultClockingReference(const ModuleDecl* decl);
  void ValidateDuplicateGlobalClocking(const ModuleDecl* decl);
  void ValidateGlobalClockReference(const ModuleDecl* decl);
  void ValidateContAssignToClockvar(const ModuleDecl* decl);
  void WalkStmtsForClockvarAccess(const Stmt* s);
  void CheckClockvarAccessExpr(const Expr* e, bool is_lvalue);
  void ValidateSyncDriveForm(const ModuleDecl* decl);
  void WalkStmtsForSyncDriveForm(const Stmt* s);
  bool ExprTargetsWritableClockvar(const Expr* e) const;

  // §14.16.2: true when `name` is a plain variable that is associated with an
  // output (or inout) clockvar -- i.e. the underlying signal driven by a
  // clocking-block output. Writing to such a variable by any external driver is
  // illegal.
  bool IsOutputClockvarSignal(std::string_view name) const;
  // §14.16.2: it is illegal to drive a variable associated with an output
  // clockvar from a primitive (gate) output terminal.
  void ValidatePrimitiveDriveToClockvar(const ModuleDecl* decl);

  void ValidateAssocConcatTarget(const ModuleDecl* decl);
  void WalkStmtsForAssocConcatTarget(const Stmt* s);
  void CheckAssocConcatTargetInAssign(const Stmt* s);

  void ValidateAssocOperandInExpr(const ModuleDecl* decl);
  void WalkStmtsForAssocOperand(const Stmt* s);
  void CheckAssocOperandInBinaryExpr(const Expr* e);

  void ValidateArrayPatternElemType(const ModuleDecl* decl);
  void WalkStmtsForArrayPatternElemType(const Stmt* s);
  void CheckArrayPatternElemTypeInAssign(const Stmt* s);
  void ValidateReplicateTargetingArray(const ModuleDecl* decl);
  void WalkStmtsForReplicateTargetingArray(const Stmt* s);
  void CheckReplicateTargetingArrayInAssign(const Stmt* s);

  void ValidateArrayElementPartSelect(const ModuleDecl* decl);
  void WalkStmtsForArrayElementPartSelect(const Stmt* s);
  void WalkExprForArrayElementPartSelect(const Expr* e);
  void CheckArrayElementPartSelectNode(const Expr* e);

  void ValidateUnpackedArrayConcatNesting(const ModuleDecl* decl);
  void WalkStmtsForArrayConcatNesting(const Stmt* s);
  void CheckArrayConcatNestingInAssign(const Stmt* s);
  void CheckNullItemInArrayConcatAssign(const Stmt* s);

  void ValidateAggregateComparisons(const ModuleDecl* decl);
  void WalkExprForAggregateCompare(const Expr* expr);
  void CheckAggregateCompareOp(const Expr* expr);
  void WalkStmtsForAggregateCompare(const Stmt* s);

  void ValidateTypeRefComparisons(const ModuleDecl* decl);
  void WalkExprForTypeRefCompare(const Expr* expr);
  void CheckTypeRefCompareOp(const Expr* expr);
  void WalkStmtsForTypeRefCompare(const Stmt* s);

  void ValidateTypeRefArgs(const ModuleDecl* decl);
  void WalkExprForTypeRefArg(const Expr* expr);
  void WalkStmtsForTypeRefArg(const Stmt* s);
  void CheckTypeRefArgInner(const Expr* inner, SourceLoc loc);
  bool TypeRefArgUsesDynamicElement(const Expr* e) const;

  void ValidateTaggedUnionMembers(const ModuleDecl* decl);
  void WalkStmtsForTaggedExpr(const Stmt* s);
  void CheckTaggedExprMember(const Expr* lhs, const Expr* rhs);

  void ValidateRealOperatorRestrictions(const ModuleDecl* decl);
  void WalkExprForRealOps(const Expr* expr);
  void WalkStmtsForRealOps(const Stmt* s);

  void ValidateAssignInExprRestrictions(const ModuleDecl* decl);
  void WalkExprForAssignInExpr(const Expr* expr, bool in_event_or_cont);
  void WalkStmtsForAssignInExpr(const Stmt* s);

  void ValidateUnsizedInConcat(const ModuleDecl* decl);
  void WalkExprForUnsizedInConcat(const Expr* expr);
  void WalkStmtsForUnsizedInConcat(const Stmt* s);

  void ValidateSelectOnConcatLvalue(const ModuleDecl* decl);
  void CheckSelectOnConcatLvalue(const Expr* lhs);
  void WalkStmtsForSelectOnConcatLvalue(const Stmt* s);

  void ValidateReplicateLvalue(const ModuleDecl* decl);
  void CheckReplicateLvalue(const Expr* lhs);
  void WalkStmtsForReplicateLvalue(const Stmt* s);

  void ValidateReplicateMultiplier(const ModuleDecl* decl);
  void WalkExprForReplicateMultiplier(const Expr* expr);
  void WalkStmtsForReplicateMultiplier(const Stmt* s);

  void ValidateStringConcatLvalue(const ModuleDecl* decl);
  void CheckStringConcatLvalue(const Expr* lhs);
  void WalkStmtsForStringConcatLvalue(const Stmt* s);
  bool ConcatContainsStringElement(const Expr* expr);

  void ValidateStreamingConcatContext(const ModuleDecl* decl);
  void WalkExprForStreamingContext(const Expr* expr, bool is_valid_context);
  void WalkStmtsForStreamingContext(const Stmt* s);
  void CheckStreamingSourceTargetType(const Expr* lhs, const Expr* rhs);

  // §6.24.3: enforces the destination/source/size constraints on a bit-stream
  // cast. Walks every expression in a module and rejects illegal forms before
  // the simulator ever sees them.
  void ValidateBitStreamCast(const ModuleDecl* decl);
  void WalkExprForBitStreamCast(const Expr* expr);
  void WalkStmtsForBitStreamCast(const Stmt* s);
  void CheckBitStreamCastExpr(const Expr* expr);

  void ValidateScopeRules(const ModuleDecl* decl);

  // Returns true when `name` is resolvable against any of the module-level name
  // sets (declared signals, ports, constants, enum members, specparams,
  // classes, tasks, functions, interface instances, or checker instances).
  // Callers handle scope-local names (e.g. block-locals or prior arguments)
  // before consulting this shared check.
  bool IsNameInModuleScope(std::string_view name) const;

  void ValidateHierRefIntoChecker(const ModuleDecl* decl);

  void ValidateHierRefInstanceArray(const ModuleDecl* decl);

  void ValidateHierRefToAutomatic(const ModuleDecl* decl);

  void ValidateHierRefIntoProgram(const ModuleDecl* decl);

  void ValidateProgramSubroutineCall(const ModuleDecl* decl);

  ModuleItem* FindCuScopeItem(std::string_view name) const;

  void ApplyBindDirectives(RtlirModule* top);
  // §23.11: the invariant context carried through the bind hierarchy walk --
  // the set of bind directives being matched, the modules already visited
  // (cycle guard), and the directives that have matched a target so far.
  struct BindWalkCtx {
    const std::vector<BindDirective*>& binds;
    std::unordered_set<RtlirModule*>& visited;
    std::unordered_set<BindDirective*>& applied;
  };
  void WalkForBind(RtlirModule* mod, const std::string& hier_path,
                   bool under_bind, BindWalkCtx& ctx);
  void ApplyBindInstance(BindDirective* bd, RtlirModule* target);

  void ValidateModportExportConflicts(RtlirModule* top);
  void WalkForExportConflicts(RtlirModule* mod,
                              std::unordered_set<RtlirModule*>& visited);

  Arena& arena_;
  DiagEngine& diag_;
  CompilationUnit* unit_;
  std::string gen_prefix_;

  // §20.10.1: any $fatal or $error elaboration severity task that survives
  // generate-construct expansion sets this to true. Propagated onto the
  // resulting RtlirDesign so the simulator can refuse to start.
  bool elab_simulation_blocked_ = false;

  // §20.10.1: details of the most recent elaboration severity task call.
  // Propagated onto the RtlirDesign so observers can inspect what was
  // emitted (severity tag, source location, hierarchical scope, user text).
  std::string elab_last_severity_;
  std::string elab_last_severity_msg_;
  std::string elab_last_severity_scope_;
  SourceLoc elab_last_severity_loc_;

  std::vector<std::string> library_order_;

  bool library_order_strict_ = false;

  // A cell selection clause paired with a use expansion clause (§33.4.1.4,
  // §33.4.1.6). src_lib is the library qualifying the selected cell, empty when
  // the clause is unqualified and so applies to the cell in any library.
  // use_lib/use_cell name the binding target; an empty use_lib means the
  // library is inherited from the parent cell.
  struct CellUseOverride {
    std::string src_lib;
    std::string use_lib;
    std::string use_cell;
  };
  std::unordered_map<std::string, CellUseOverride> cell_clause_use_overrides_;

  // A cell selection clause paired with a liblist expansion clause: the named
  // cell is searched for in this ordered library list (§33.4.1.4, §33.4.1.5).
  std::unordered_map<std::string, std::vector<std::string>>
      cell_clause_liblist_overrides_;

  std::vector<std::pair<std::string, std::vector<std::string>>>
      instance_liblist_overrides_;

  std::vector<std::tuple<std::string, std::string, std::string>>
      instance_use_overrides_;

  // A configuration's parameter overrides for one instance path (§33.4.3).
  // reset_all marks an empty "#()" list that returns every parameter to its
  // module default; within params, a null expression returns that single
  // parameter to its default while a present expression supplies a new value.
  struct ConfigParamOverride {
    std::string inst_path;
    bool reset_all = false;
    std::vector<std::pair<std::string_view, Expr*>> params;
  };
  std::vector<ConfigParamOverride> instance_param_overrides_;

  // Literal values of the localparams declared in the configuration being
  // elaborated, used to evaluate parameter-override expressions (§33.4.3).
  ScopeMap config_localparam_scope_;

  // Applies any configuration parameter overrides registered for the instance
  // currently being elaborated (named by current_inst_path_) on top of the
  // overrides written at the instantiation, recording which parameters end up
  // fixed by the configuration. Config overrides win over the instantiation's
  // own values, and an empty override returns a parameter to its module
  // default (§33.4.3).
  void ApplyConfigParamOverrides(const ModuleDecl* child_decl,
                                 ParamList& child_params,
                                 const ScopeMap& parent_scope,
                                 std::vector<std::string_view>& locked);

  std::string current_inst_path_;
  // Library of the cell currently being elaborated; the parent cell's library
  // while its child instances are resolved (§33.4.1.5, §33.4.1.6).
  std::string current_library_;
  // True while elaborating from a configuration, so config-specific library
  // resolution rules apply (§33.4.1.5).
  bool in_config_elaboration_ = false;
  TypedefMap typedefs_;
  // §6.24.3: names of typedefs whose unpacked dimensions designate an
  // associative array. A bit-stream cast must reject any such typedef as a
  // destination type.
  std::unordered_set<std::string_view> assoc_typedef_names_;
  // §6.24.3: total bit width of a typedef whose unpacked dimensions are all
  // fixed-size (no dynamic, queue, or associative dims). Used to detect
  // fixed-size mismatch when the destination of a bit-stream cast is an
  // unpacked-array typedef.
  std::unordered_map<std::string_view, uint32_t> fixed_unpacked_typedef_widths_;
  std::unordered_set<std::string_view> cu_scope_names_;
  ScopeMap cu_param_scope_;

  // Public so free helpers (e.g. FormalArrayInfo in
  // elaborator_validate_class_array_*.cpp) can name and build this type.
 public:
  struct VarArrayInfo {
    DataTypeKind elem_type = DataTypeKind::kImplicit;
    uint32_t unpacked_size = 0;
    uint32_t num_unpacked_dims = 0;
    uint32_t elem_width = 0;
    bool elem_is_signed = false;
    bool elem_is_4state = true;
    bool is_dynamic = false;
    bool is_assoc = false;
    std::string_view assoc_index_type;
    std::vector<uint32_t> dim_sizes;
    bool is_queue = false;
  };

 private:
  std::unordered_set<std::string_view> declared_names_;
  std::unordered_set<std::string_view> net_names_;
  std::unordered_map<std::string_view, SourceLoc> cont_assign_targets_;
  std::unordered_map<std::string_view, SourceLoc> proc_assign_targets_;
  std::unordered_map<std::string_view, DataTypeKind> var_types_;
  std::unordered_map<std::string_view, VarArrayInfo> var_array_info_;
  std::unordered_map<std::string_view, const ModuleItem*> dpi_import_decls_;

  std::unordered_set<std::string_view> packed_array_vars_;
  std::unordered_set<std::string_view> specparam_names_;
  std::unordered_set<std::string_view> enum_var_names_;
  std::unordered_set<std::string_view> enum_member_names_;
  std::unordered_set<std::string_view> const_names_;
  // §6.19: const *variables* only (not parameters/specparams), which unlike
  // elaboration-time constants may not appear in an enum named-constant value.
  std::unordered_set<std::string_view> const_var_names_;

  std::unordered_map<std::string_view, DataTypeKind> forward_typedef_kinds_;
  std::unordered_set<std::string_view> class_names_;
  std::unordered_set<std::string_view> parameterized_class_names_;
  std::unordered_set<std::string_view> class_var_names_;
  std::unordered_map<std::string_view, std::string_view> class_var_types_;
  std::unordered_set<std::string_view> var_init_names_;
  std::unordered_map<std::string_view, SourceLoc> output_port_targets_;
  std::unordered_set<std::string_view> nettype_net_names_;
  std::unordered_set<std::string_view> nettype_names_;
  std::unordered_map<std::string_view, std::string_view> nettype_resolve_funcs_;
  std::unordered_map<std::string_view, std::string_view> nettype_canonical_;
  std::unordered_set<std::string_view> interconnect_names_;
  std::unordered_set<std::string_view> scalar_var_names_;
  std::unordered_set<std::string_view> task_names_;
  std::unordered_set<std::string_view> sequence_names_;
  // §16.12 / §F.4.1: registry of property and sequence declarations used
  // to flatten an instance's body for legality checks.
  PropertyRegistry property_registry_;

  std::unordered_map<std::string_view, const ModuleItem*> func_decls_;
  std::unordered_map<std::string_view, std::string_view> var_named_types_;
  std::set<std::pair<std::string_view, std::string_view>> alias_pairs_;

  std::unordered_set<std::string_view> non_ansi_complete_ports_;
  std::unordered_map<std::string_view, uint32_t> non_ansi_partial_ports_;
  // Non-ANSI partial ports whose port direction declaration carried `signed`.
  std::unordered_set<std::string_view> non_ansi_signed_ports_;

  std::unordered_set<std::string_view> ansi_port_names_;

  std::unordered_map<std::string_view, std::string_view> interface_inst_types_;

  std::unordered_map<std::string_view, std::string_view>
      vi_var_interface_types_;

  std::unordered_map<std::string_view, std::string_view> vi_var_modports_;

  // §25.9: explicit parameter value overrides, evaluated to constants, for
  // virtual interface variables and for interface instances. Used to verify
  // that the actual parameter values match for a virtual interface and the
  // interface (instance or other virtual interface) it is assigned from.
  std::unordered_map<std::string_view, std::vector<int64_t>>
      vi_var_param_values_;
  std::unordered_map<std::string_view, std::vector<int64_t>>
      interface_inst_param_values_;

  // §25.9: interface instances targeted by a defparam declared outside the
  // interface; such an instance shall not be assigned to a virtual interface.
  std::unordered_set<std::string_view> vi_external_defparam_insts_;

  std::unordered_set<std::string_view> checker_inst_names_;
  std::unordered_set<std::string_view> program_inst_names_;
  std::unordered_set<std::string_view> auto_task_func_names_;
  std::unordered_map<std::string_view, ModuleDecl*> nested_module_decls_;

  std::unordered_map<std::string_view, std::unordered_set<std::string_view>>
      pkg_provided_names_;

  std::unordered_map<std::string_view, std::pair<std::string_view, SourceLoc>>
      explicit_imports_;

  std::vector<std::string_view> wildcard_packages_;

  std::unordered_map<std::string_view, SourceLoc> wildcard_claimed_;

  struct ClockingSignalInfo {
    Direction direction;
  };
  std::unordered_map<std::string_view,
                     std::unordered_map<std::string_view, ClockingSignalInfo>>
      clocking_signals_;

  struct PendingGenerate {
    ModuleItem* item;
    RtlirModule* mod;
  };
  std::vector<PendingGenerate> pending_generates_;

  std::set<std::tuple<RtlirModule*, const ModuleItem*, size_t>>
      applied_defparams_;

  struct EarlyDefparamResolution {
    RtlirModule* root;
    const Expr* path_expr;
    RtlirParamDecl* resolved;
    SourceLoc loc;
  };
  std::vector<EarlyDefparamResolution> early_defparam_resolutions_;
};

}  // namespace delta
