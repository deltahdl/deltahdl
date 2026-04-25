#pragma once

#include <cstdint>
#include <set>
#include <string>
#include <string_view>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

// Forward declarations
class Arena;
class DiagEngine;
struct RtlirDesign;
struct RtlirModule;
struct RtlirVariable;
struct RtlirModuleInst;
struct RtlirParamDecl;

/// Elaborator transforms a parsed AST (CompilationUnit) into the
/// elaborated RTLIR representation.  Phase 1 supports single-module
/// designs without parameterized instantiation.
class Elaborator {
 public:
  using ParamList = std::vector<std::pair<std::string_view, int64_t>>;

  Elaborator(Arena& arena, DiagEngine& diag, CompilationUnit* unit);

  /// Elaborate the design rooted at the given top module.
  /// Returns nullptr on failure (diagnostics emitted via DiagEngine).
  RtlirDesign* Elaborate(std::string_view top_module_name);

  /// §33.5.4: Elaborate the design driven by `cfg`'s `design` statement.
  /// Each cell named in the design statement becomes a top-level module
  /// of the resulting RtlirDesign, regardless of any uninstantiated
  /// cells that happen to share the source files.
  RtlirDesign* Elaborate(const ConfigDecl* cfg);

 private:
  /// Run the one-shot validation passes that must precede any module
  /// elaboration step, regardless of how the top modules were chosen.
  void RunPreElaborationValidations();

  /// Build an RtlirDesign rooted at the given top module declarations.
  /// Shared by both public `Elaborate` overloads.
  RtlirDesign* ElaborateTops(const std::vector<ModuleDecl*>& top_decls);

  /// §3.13: Check definitions and package name spaces for duplicates.
  void ValidateNameSpaces();

  /// §33.4.1.1: validate every config's design statement: cells named
  /// in `design` cannot be configurations themselves, and an omitted
  /// library identifier defaults to the library that contains the
  /// config.
  void ValidateConfigDesignStatements();

  /// §33.4.1.2: each config may contain at most one default clause.
  void ValidateConfigDefaultClauses();

  /// §33.4.1.3: each `instance` clause's hierarchical name must start
  /// at a cell named in the config's `design` statement.
  void ValidateConfigInstanceClauses();

  /// §33.4.1.4: a `cell` clause that includes a library qualifier on
  /// the cell name cannot use a `liblist` expansion clause.
  void ValidateConfigCellClauses();

  /// §33.4.2: an instance clause cannot specify a hierarchical path
  /// inside a subhierarchy already delegated to another config via
  /// `instance ... use ...:config`.
  void ValidateConfigHierarchicalRules();

  /// §33.4.3 item 1: each `localparam` declared in a configuration
  /// must be assigned a literal value (no expressions, no identifier
  /// references).
  void ValidateConfigLocalparams();

  /// §33.4.3 items 3, 5, 6: validate value expressions that override
  /// parameters via a `use #(.NAME(value))` clause.  A hierarchical
  /// identifier must be the entire expression; the path may not pass
  /// through array-of-instances scopes; and only built-in (system)
  /// constant functions may appear.
  void ValidateConfigParamOverrides();

  /// §24.6: Anonymous program items share the surrounding package or
  /// compilation-unit name space; collisions with that surrounding scope
  /// are an error.
  void ValidateAnonymousProgramNameSharing();

  /// §26.2: Reject package items that are nets with implicit continuous
  /// assignments or processes (initial, final, always*).
  void ValidatePackageItems();

  /// §26.6: Validate package export declarations. For `export p::name`:
  /// the name must exist in `p` as an import candidate, and the package must
  /// import it either explicitly (`import p::name`) or via wildcard
  /// (`import p::*`). An export can precede its matching import.
  void ValidatePackageExports();

  /// §26.3: Validate package import declarations inside a module:
  ///   - explicit-import collisions with local decls and other explicit imports
  ///   - local decl that shadows a name already referenced via wildcard import
  ///   - ambiguous references resolvable through multiple wildcard imports
  void ValidatePackageImportRules(const ModuleDecl* decl);

  /// §26.3: Reject hierarchical references that resolve to a name imported
  /// (explicitly or via wildcard) into a child module.
  void ValidateHierRefToImportedName(const ModuleDecl* decl,
                                     const RtlirModule* mod);

  /// §26.4: Make package items imported in a module/interface/program header
  /// visible to the parameter and port declarations that follow. Applied
  /// before parameter and port elaboration.
  void ApplyHeaderImports(const ModuleDecl* decl);

  /// §25.5.4: Validate per-modport port-id uniqueness and reject constant
  /// port expressions paired with output or inout direction.
  void ValidateModports();

  /// §25.6: Reject ref-direction module ports used as specify-block
  /// terminals.
  void ValidateSpecifyBlocks();

  /// §3.12.1: Register CU-scope typedefs/classes before module elaboration.
  void RegisterCuScopeItems();

  /// §23.5: Resolve extern module declarations against actual definitions.
  void ResolveExternModules();

  /// Find a module declaration by name in the compilation unit.
  ModuleDecl* FindModule(std::string_view name) const;

  /// Find a module by name, checking nested module scope first.
  ModuleDecl* FindModuleInScope(std::string_view name) const;

  /// Elaborate a single module declaration into an RtlirModule.
  RtlirModule* ElaborateModule(const ModuleDecl* decl, const ParamList& params);

  /// Populate ports from module declaration port list.
  void ElaboratePorts(const ModuleDecl* decl, RtlirModule* mod);

  /// Elaborate a single module item into RTLIR.
  void ElaborateItem(ModuleItem* item, RtlirModule* mod);
  void ElaborateParamDecl(ModuleItem* item, RtlirModule* mod);
  void ElaborateNetDecl(ModuleItem* item, RtlirModule* mod);
  void ElaborateVarDecl(ModuleItem* item, RtlirModule* mod);
  void SetStructTypeInfo(const ModuleItem* item, RtlirVariable& var);
  void ElaborateContAssign(ModuleItem* item, RtlirModule* mod);
  void ValidateContAssignIdentLhs(ModuleItem* item, RtlirModule* mod);
  void ValidateContAssignNettypeAndDelay(ModuleItem* item);
  void ValidateContAssignDriveStrength(ModuleItem* item, RtlirModule* mod);
  void ElaborateSpecparam(ModuleItem* item, RtlirModule* mod);

  /// Elaborate a typedef item (e.g. enum constants).
  void ElaborateTypedef(ModuleItem* item, RtlirModule* mod);

  /// §6.6.7: Elaborate a nettype declaration.
  void ElaborateNettypeDecl(ModuleItem* item, RtlirModule* mod);

  /// §6.22.6: Return true if two nettype names refer to matching nettypes.
  bool NettypesMatch(std::string_view a, std::string_view b) const;

  /// Walk module items and populate nets, vars, assigns, processes.
  void ElaborateItems(const ModuleDecl* decl, RtlirModule* mod);

  /// Elaborate a module instantiation (resolve child, bind ports).
  void ElaborateModuleInst(ModuleItem* item, RtlirModule* mod);

  /// §29.3: Find a UDP declaration by name in the compilation unit.
  UdpDecl* FindUdpByName(std::string_view name) const;

  /// §29.3: A UDP may be instantiated before its definition appears in the
  /// source; the parser records such forward references as module instances.
  /// Rewrite any item whose `inst_module` matches a compilation-unit UDP into
  /// a UDP-instance shape so the elaborator and simulator see them uniformly.
  void ReclassifyForwardUdpInstances(const ModuleDecl* decl);

  /// Create a pull0/pull1 constant expression for §22.9.
  Expr* MakePullExpr(NetType drive);
  Expr* MakeHighZExpr();

  /// Bind instance ports to continuous assignments.
  void BindPorts(RtlirModuleInst& inst, const ModuleItem* item,
                 RtlirModule* parent_mod);

  /// §23.3.3.1: Warn when a port's declared direction does not match usage.
  void CheckPortCoercion(const RtlirModuleInst& inst, SourceLoc loc);

  void CheckUwirePortMerge(const RtlirModuleInst& inst,
                           const ModuleItem* item, RtlirModule* parent_mod);

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

  /// Build a scope map from CU-scope and module parameters.
  ScopeMap BuildParamScope(const RtlirModule* mod) const;

  /// Expand a generate-if block using constant evaluation.
  void ElaborateGenerateIf(ModuleItem* item, RtlirModule* mod,
                           const ScopeMap& scope);

  /// Expand a generate-case block using constant evaluation.
  void ElaborateGenerateCase(ModuleItem* item, RtlirModule* mod,
                             const ScopeMap& scope);

  /// Expand a generate-for loop using constant evaluation.
  void ElaborateGenerateFor(ModuleItem* item, RtlirModule* mod,
                            const ScopeMap& scope);

  /// Elaborate a list of generate-body items, recursing into nested generates.
  void ElaborateGenerateItems(const std::vector<ModuleItem*>& items,
                              RtlirModule* mod, const ScopeMap& scope);

  /// §27.6: Assign `genblk<n>` names to unnamed generate constructs in the
  /// module's scope, numbering them in textual order.  When the default name
  /// collides with an explicitly declared identifier in the same scope,
  /// leading zeros are inserted in front of <n> until the name is unique.
  void AssignGenerateBlockNames(const ModuleDecl* decl);

  /// Apply defparam overrides after hierarchy is built.
  void ApplyDefparams(RtlirModule* mod, const ModuleDecl* decl);

  /// Walk the hierarchy and apply each instance's defparams.
  void ApplyDefparamsRecursively(RtlirModule* mod);

  /// Walk the hierarchy emitting warnings for defparams whose target
  /// never resolved across all iterations of the elaboration algorithm.
  void WarnUnresolvedDefparams(RtlirModule* mod);

  /// §23.10.4.2: error if any early-resolved defparam path now binds to a
  /// different parameter once elaboration has completed.
  void VerifyEarlyResolvedDefparams();

  /// Evaluate a deferred generate construct.
  void ProcessPendingGenerate(ModuleItem* item, RtlirModule* mod);

  /// Resolve a hierarchical path to find the target module and param name.
  /// If out_mod is non-null, receives the module that owns the returned param.
  RtlirParamDecl* ResolveDefparamPath(RtlirModule* root, const Expr* path_expr,
                                      RtlirModule** out_mod = nullptr);

  /// §23.10.3: Re-resolve non-override parameters and localparams so that
  /// values whose expressions depend on a just-overridden parameter pick up
  /// the new scope.
  void RecomputeDependentParams(RtlirModule* mod);

  /// §6.10: Create an implicit scalar net if the identifier is undeclared.
  /// Returns false if `default_nettype none and the name is undeclared.
  bool MaybeCreateImplicitNet(std::string_view name, SourceLoc loc,
                              RtlirModule* mod);

  /// Return a scoped name (prefixed during generate-for expansion).
  std::string_view ScopedName(std::string_view base);

  /// §6.23: Resolve type(expr) to concrete type kind.
  void ResolveTypeRef(ModuleItem* item, const RtlirModule* mod);

  /// §6.25: Resolve cls#(type_arg)::member to a concrete DataType.
  bool ResolveParameterizedType(DataType& dtype);

  /// Validate array assignment pattern element count (§5.11).
  void ValidateArrayInitPattern(const ModuleItem* item);
  void ValidateStructInitPattern(const ModuleItem* item);

  /// Run all post-item validation checks for a module (§6).
  void ValidateModuleConstraints(const ModuleDecl* decl);

  /// Validate enum declaration constraints (§6.19).
  void ValidateEnumDecl(const DataType& dtype, SourceLoc loc);

  /// Validate packed struct default member values (§7.2.2).
  void ValidatePackedStructDefaults(const DataType& dtype, SourceLoc loc);

  /// §7.2.2: Unpacked struct containing union: no member defaults.
  void ValidateUnpackedStructWithUnionDefaults(const DataType& dtype,
                                               SourceLoc loc);

  /// §7.2.2: Struct member defaults must be constant expressions.
  void ValidateStructMemberDefaultsConstant(const DataType& dtype,
                                            SourceLoc loc);

  /// §7.2, footnote 20: void member only in tagged unions.
  void ValidateVoidMembers(const DataType& dtype, SourceLoc loc);

  /// §7.2, footnote 20: random qualifier only in unpacked structures.
  void ValidateRandQualifiers(const DataType& dtype, SourceLoc loc);

  /// §7.2, footnote 17: packed dimension requires packed/soft keyword.
  void ValidatePackedDimRequiresPackedKeyword(const DataType& dtype,
                                              SourceLoc loc);

  /// §7.2.1/§7.3.1: Only packed/integer types in packed structures/unions.
  void ValidatePackedStructMemberTypes(const DataType& dtype, SourceLoc loc);

  /// §7.3: Chandle types only in tagged unions.
  void ValidateChandleInUnion(const DataType& dtype, SourceLoc loc);

  /// §25.9: Virtual interfaces shall not be used as members of unions.
  void ValidateVirtualInterfaceInUnion(const DataType& dtype, SourceLoc loc);

  /// §25.9: Virtual interface variable cannot appear in continuous assignment.
  void ValidateVirtualInterfaceContAssign(const ModuleItem* item);

  /// §25.9: Virtual interface variable cannot appear in sensitivity list.
  void ValidateVirtualInterfaceSensitivity(const ModuleItem* item);

  /// §25.9: Allowed operations on virtual interface variables (=, ==, !=).
  void ValidateVirtualInterfaceOps(const ModuleDecl* decl);

  /// §25.9: Walk statements for virtual interface operation restrictions.
  void WalkStmtsForVirtualInterfaceOps(const Stmt* s);

  /// §25.9.1: Validate vif.clocking_block.signal member-access chains and
  /// array-of-virtual-interface assignment-pattern initializers.
  void ValidateVirtualInterfaceClocking(const ModuleDecl* decl);

  /// §25.9.1: Walk statements to validate vif-clocking access and array-of-vif
  /// assignment-pattern initializers.
  void WalkStmtsForVirtualInterfaceClocking(const Stmt* s);

  /// §25.9.1: Validate an array-of-virtual-interface assignment-pattern
  /// initializer on a block-level variable declaration statement.
  void ValidateArrayOfVifInitStmt(const Stmt* s);

  /// §25.10: Validate member access through interface ports and virtual
  /// interfaces against any selected modport's member list.
  void ValidateInterfaceObjectAccess(const ModuleDecl* decl);

  /// Validate packed union constraints (§7.3.1).
  void ValidatePackedUnion(const DataType& dtype, SourceLoc loc);

  /// §6.9.1: Range bounds shall not contain x or z.
  void ValidatePackedDimRange(const DataType& dtype, SourceLoc loc);

  /// §7.4.2: Unpacked dimension ranges shall not contain x or z.
  void ValidateUnpackedDimRange(const std::vector<Expr*>& dims, SourceLoc loc);

  /// §7.4.1: Predefined-width types shall not have packed dims.
  void ValidatePackedDimOnPredefinedType(const DataType& dtype, SourceLoc loc);

  /// §7.6, §7.9.9: Array assignment compatibility checks.
  void ValidateArrayAssignments(const ModuleDecl* decl);
  void ValidateOneArrayAssignment(const ModuleItem* item);
  void CheckArrayAssignExprs(const Expr* lhs, const Expr* rhs, SourceLoc loc);
  void WalkStmtsForArrayAssign(const Stmt* s);

  /// §7.4.6: Associative arrays shall not be sliced.
  void ValidateAssocArraySlices(const ModuleDecl* decl);

  /// §7.9.4–§7.9.7: Traversal methods not allowed on wildcard assoc arrays.
  void ValidateAssocWildcardTraversal(const ModuleDecl* decl);

  /// §7.8.5: real/shortreal as associative array index type is illegal.
  void ValidateAssocIndexType(const ModuleItem* item);

  /// §7.6/§7.9.9: Track array metadata for assignment compatibility.
  void TrackVarArrayInfo(const ModuleItem* item, const RtlirVariable& var);

  /// §8.4/§6.19: Validate class tracking, enum, struct/union types on var decl.
  void ValidateVarDeclTypes(ModuleItem* item);

  /// Validate a single enum member literal (§6.19).
  bool ValidateEnumLiteral(const EnumMember& member, uint32_t base_width,
                           bool is_2state);

  /// Validate edge events don't reference real types (§6.12).
  void ValidateEdgeOnReal(const ModuleItem* item);

  /// Per-item validation within ValidateModuleConstraints.
  void ValidateItemConstraints(const ModuleItem* item);

  /// §6.14: chandle cannot be used in continuous assignment.
  void ValidateChandleContAssign(const ModuleItem* item);

  /// §6.14: chandle cannot appear in event expression.
  void ValidateChandleSensitivity(const ModuleItem* item);

  /// §6.14: chandle operator and assignment restrictions.
  void ValidateChandleOps(const ModuleDecl* decl);
  void WalkStmtsForChandleOps(const Stmt* s);

  /// §6.6.8: interconnect net cannot appear in continuous assignment.
  void ValidateInterconnectContAssign(const ModuleItem* item);

  /// Check for mixed continuous/procedural assignments (§6.5).
  void ValidateMixedAssignments();

  /// §10.2 Table 10-1: Procedural assignment to a net is illegal.
  void ValidateProceduralNetAssign();
  void ValidateDynamicArrayNba(const ModuleDecl* decl);

  /// §10.2 Table 10-1: Continuous assignment LHS selects must be constant.
  void ValidateContAssignConstSelect(const ModuleDecl* decl);

  /// §A.1.4: Validate elaboration severity system task (finish_number).
  void ValidateElabSystemTask(const ModuleItem* item);

  /// §10.11: Validate alias statement operands.
  void ValidateAlias(const ModuleItem* item, RtlirModule* mod);

  /// Check specparam not used in parameter expressions (§6.20.5).
  void ValidateSpecparamInParams(const ModuleDecl* decl);

  /// §6.20.2: Validate value parameter declarations.
  void ValidateValueParams(const ModuleDecl* decl, const RtlirModule* mod);

  /// §9.2.2.2: Check multi-driver violations on always_comb LHS variables.
  void CheckAlwaysCombMultiDriver(const ModuleDecl* decl, RtlirModule* mod);

  /// §9.6.2 R8: Validate disable statements do not target functions.
  void ValidateDisableTargets(const ModuleDecl* decl);

  /// §13.2/§13.4.1/§13.4.4: Validate function/task body constraints.
  void ValidateFunctionBody(const ModuleItem* item);
  /// §13.4.3: Validate constant function calls in parameter expressions.
  void ValidateConstantFunctionCalls(const ModuleDecl* decl);
  /// §13.5: Validate subroutine call arguments.
  void ValidateSubroutineCallArgs(const ModuleDecl* decl);

  /// §7.9.10: Validate array argument type compatibility at call sites.
  void ValidateArrayArgTypes(const ModuleDecl* decl);

  /// Track enum type info for a variable declaration.
  void TrackEnumVariable(const ModuleItem* item);

  /// Check assignments to enum vars in a statement tree (§6.19.3/§6.19.4).
  void ValidateEnumAssignments(const ModuleDecl* decl);

  /// Walk statement tree checking enum assignment constraints.
  void WalkStmtsForEnumAssign(const Stmt* s);

  /// §6.20.6: Check assignments to const variables.
  void ValidateConstAssignments(const ModuleDecl* decl);

  /// Walk statement tree checking const assignment constraints.
  void WalkStmtsForConstAssign(const Stmt* s);

  /// Check a single assignment statement for enum type violations.
  void CheckEnumAssignStmt(const Stmt* s);

  /// §8.4: Validate class handle operator restrictions.
  void ValidateClassHandleOps(const ModuleDecl* decl);

  /// Walk statement tree checking class handle operation constraints.
  void WalkStmtsForClassHandleOps(const Stmt* s);

  /// §8.4: Class handle cannot appear in continuous assignment.
  void ValidateClassHandleContAssign(const ModuleItem* item);

  /// §8.10: Static method bodies shall not reference 'this' or 'super'.
  void ValidateStaticMethodBodies(const ModuleDecl* decl);
  void ValidateOneClassStaticMethods(const ClassDecl* cls);

  /// §8.11: 'this' shall only be used within non-static class methods.
  void ValidateThisUsage(const ModuleDecl* decl);
  void ValidateThisInItem(const ModuleItem* item);

  /// §8.13: A class declared :final shall not be extended.
  void ValidateFinalClassExtension();

  /// §8.7: Validate class method function bodies (nonblocking, etc.).
  void ValidateClassMethodBodies(const ModuleDecl* decl);

  /// §8.17: Validate chaining constructor rules.
  void ValidateChainingConstructors();
  void ValidateOneClassChainingCtor(const ClassDecl* cls);

  /// §8.18: Validate local/protected access from module-level code.
  void ValidateLocalProtectedAccess(const ModuleDecl* decl);

  /// §8.19: Validate constant class property rules.
  void ValidateConstClassProperties();

  /// §8.20: Validate virtual method override rules.
  void ValidateVirtualMethodOverrides();
  void ValidateOneMethodOverride(const ClassDecl* cls, const ClassMember* m);

  /// §8.21: Validate abstract class and pure virtual method rules.
  void ValidateAbstractClassRules();
  void ValidateAbstractClassUnimplemented(const ClassDecl* cls);

  /// §8.24: Validate out-of-block method declarations.
  void ValidateOutOfBlockDeclarations();

  /// §8.25.1: Validate parameterized class scope resolution.
  void ValidateParameterizedScopeResolution(const ModuleDecl* decl);

  /// §8.26: Validate interface class rules.
  void ValidateInterfaceClassRules();

  /// §8.27: Validate forward class typedefs are resolved.
  void ValidateForwardClassTypedefs();
  void ValidateInterfaceClassMembers(const ClassDecl* cls);
  void ValidateInterfaceClassInheritance(const ClassDecl* cls);
  void ValidateRegularClassInheritance(const ClassDecl* cls);
  void ValidateImplementsInterfaceMethods(const ClassDecl* cls);

  void ValidateSequenceEventArgs(const ModuleDecl* decl);

  /// §14.3: Validate clocking block declaration constraints.
  void ValidateClockingBlock(ModuleItem* item);

  /// §14.3: Validate clockvar access direction rules.
  void ValidateClockvarAccess(const ModuleDecl* decl);
  void ValidateCycleDelayDefaultClocking(const ModuleDecl* decl);
  void ValidateDuplicateDefaultClocking(const ModuleDecl* decl);
  void ValidateDuplicateGlobalClocking(const ModuleDecl* decl);
  void ValidateContAssignToClockvar(const ModuleDecl* decl);
  void WalkStmtsForClockvarAccess(const Stmt* s);
  void CheckClockvarAccessExpr(const Expr* e, bool is_lvalue);

  /// §10.10: Reject unpacked array concatenation targeting associative arrays.
  void ValidateAssocConcatTarget(const ModuleDecl* decl);
  void WalkStmtsForAssocConcatTarget(const Stmt* s);
  void CheckAssocConcatTargetInAssign(const Stmt* s);

  /// §10.10.1: Reject array items in assignment patterns targeting unpacked
  /// arrays, and reject replication targeting unpacked arrays.
  void ValidateArrayPatternElemType(const ModuleDecl* decl);
  void WalkStmtsForArrayPatternElemType(const Stmt* s);
  void CheckArrayPatternElemTypeInAssign(const Stmt* s);
  void ValidateReplicateTargetingArray(const ModuleDecl* decl);
  void WalkStmtsForReplicateTargetingArray(const Stmt* s);
  void CheckReplicateTargetingArrayInAssign(const Stmt* s);

  /// §10.10.3: Validate nesting of unpacked array concatenations.
  void ValidateUnpackedArrayConcatNesting(const ModuleDecl* decl);
  void WalkStmtsForArrayConcatNesting(const Stmt* s);
  void CheckArrayConcatNestingInAssign(const Stmt* s);

  /// §11.2.2: Validate aggregate expression comparison type equivalence.
  void ValidateAggregateComparisons(const ModuleDecl* decl);
  void WalkExprForAggregateCompare(const Expr* expr);
  void CheckAggregateCompareOp(const Expr* expr);
  void WalkStmtsForAggregateCompare(const Stmt* s);

  /// §11.3.1: Validate operators not permitted on real operands.
  void ValidateRealOperatorRestrictions(const ModuleDecl* decl);
  void WalkExprForRealOps(const Expr* expr);
  void WalkStmtsForRealOps(const Stmt* s);

  /// §11.3.6: Validate assignment-in-expression restrictions.
  void ValidateAssignInExprRestrictions(const ModuleDecl* decl);
  void WalkExprForAssignInExpr(const Expr* expr, bool in_event_or_cont);
  void WalkStmtsForAssignInExpr(const Stmt* s);

  /// §11.4.12: Unsized constants not allowed in concatenations.
  void ValidateUnsizedInConcat(const ModuleDecl* decl);
  void WalkExprForUnsizedInConcat(const Expr* expr);
  void WalkStmtsForUnsizedInConcat(const Stmt* s);

  /// §11.4.12: Select of concatenation shall not be an lvalue.
  void ValidateSelectOnConcatLvalue(const ModuleDecl* decl);
  void CheckSelectOnConcatLvalue(const Expr* lhs);
  void WalkStmtsForSelectOnConcatLvalue(const Stmt* s);

  /// §11.4.12.1: Replication shall not be an lvalue.
  void ValidateReplicateLvalue(const ModuleDecl* decl);
  void CheckReplicateLvalue(const Expr* lhs);
  void WalkStmtsForReplicateLvalue(const Stmt* s);

  /// §11.4.12.1: Replication multiplier constraints.
  void ValidateReplicateMultiplier(const ModuleDecl* decl);
  void WalkExprForReplicateMultiplier(const Expr* expr);
  void WalkStmtsForReplicateMultiplier(const Stmt* s);

  /// §11.4.12.2: String concatenation shall not be an lvalue.
  void ValidateStringConcatLvalue(const ModuleDecl* decl);
  void CheckStringConcatLvalue(const Expr* lhs);
  void WalkStmtsForStringConcatLvalue(const Stmt* s);
  bool ConcatContainsStringElement(const Expr* expr);

  /// §11.4.14: Streaming concatenation context restrictions.
  void ValidateStreamingConcatContext(const ModuleDecl* decl);
  void WalkExprForStreamingContext(const Expr* expr, bool is_valid_context);
  void WalkStmtsForStreamingContext(const Stmt* s);

  /// §23.9: Named block labels share the scope's name space; direct
  /// variable references must resolve within the current module scope.
  void ValidateScopeRules(const ModuleDecl* decl);

  /// §23.6 R15: Hierarchical references into checkers prohibited.
  void ValidateHierRefIntoChecker(const ModuleDecl* decl);

  /// §23.6 R12: Objects in automatic tasks/functions inaccessible by hier ref.
  void ValidateHierRefToAutomatic(const ModuleDecl* decl);

  /// §24.3: Hierarchical references to program signals from outside the
  /// program scope are not permitted.
  void ValidateHierRefIntoProgram(const ModuleDecl* decl);

  /// §24.5: Calling program subroutines from within design modules is
  /// illegal and shall result in an error.
  void ValidateProgramSubroutineCall(const ModuleDecl* decl);

  /// §3.12.1: Find a CU-scope item by name.
  ModuleItem* FindCuScopeItem(std::string_view name) const;

  /// §23.11: After elaboration, walk the hierarchy and apply bind directives.
  void ApplyBindDirectives(RtlirModule* top);
  void WalkForBind(RtlirModule* mod, const std::string& hier_path,
                   const std::vector<BindDirective*>& binds,
                   bool under_bind,
                   std::unordered_set<RtlirModule*>& visited);
  void ApplyBindInstance(BindDirective* bd, RtlirModule* target);

  /// §25.7.4: After hierarchy is built, reject multi-module exports of the
  /// same modport-exported task unless declared `extern forkjoin`, and reject
  /// any multi-module export of a function.
  void ValidateModportExportConflicts(RtlirModule* top);
  void WalkForExportConflicts(RtlirModule* mod,
                              std::unordered_set<RtlirModule*>& visited);

  Arena& arena_;
  DiagEngine& diag_;
  CompilationUnit* unit_;
  std::string gen_prefix_;
  TypedefMap typedefs_;
  std::unordered_set<std::string_view> cu_scope_names_;  // §3.12.1
  ScopeMap cu_param_scope_;  // §3.12.1

  /// §7.6: Per-variable array metadata for assignment compatibility checks.
  struct VarArrayInfo {
    DataTypeKind elem_type = DataTypeKind::kImplicit;
    uint32_t unpacked_size = 0;  // 0 = scalar or dynamic
    uint32_t num_unpacked_dims = 0;
    uint32_t elem_width = 0;
    bool is_dynamic = false;
    bool is_assoc = false;
    std::string_view assoc_index_type;  // §7.9.9: e.g. "int", "string", "*"
    std::vector<uint32_t> dim_sizes;
  };

  // Per-module validation state (cleared in ElaborateItems).
  std::unordered_set<std::string_view> declared_names_;
  std::unordered_set<std::string_view> net_names_;  // §10.2 Table 10-1
  std::unordered_map<std::string_view, SourceLoc> cont_assign_targets_;
  std::unordered_map<std::string_view, SourceLoc> proc_assign_targets_;
  std::unordered_map<std::string_view, DataTypeKind> var_types_;
  std::unordered_map<std::string_view, VarArrayInfo> var_array_info_;
  std::unordered_set<std::string_view> specparam_names_;
  std::unordered_set<std::string_view> enum_var_names_;
  std::unordered_set<std::string_view> enum_member_names_;
  std::unordered_set<std::string_view> const_names_;
  std::unordered_set<std::string_view> class_names_;
  std::unordered_set<std::string_view> parameterized_class_names_;  // §8.25.1
  std::unordered_set<std::string_view> class_var_names_;  // §8.4
  std::unordered_map<std::string_view, std::string_view>
      class_var_types_;  // §8.18: var name → class type name
  std::unordered_set<std::string_view> var_init_names_;     // §10.3.2
  std::unordered_map<std::string_view, SourceLoc>
      output_port_targets_;                                 // §10.3.2
  std::unordered_set<std::string_view> nettype_net_names_;  // §10.3.2
  std::unordered_set<std::string_view> nettype_names_;
  std::unordered_map<std::string_view, std::string_view>
      nettype_resolve_funcs_;  // §6.6.7: nettype name → resolution function
  std::unordered_map<std::string_view, std::string_view>
      nettype_canonical_;  // §6.22.6: nettype name → canonical base name
  std::unordered_set<std::string_view> interconnect_names_;
  std::unordered_set<std::string_view> scalar_var_names_;  // §11.5.1
  std::unordered_set<std::string_view> task_names_;  // §13.2
  std::unordered_set<std::string_view> sequence_names_;
  // §13.4.3: Function declarations by name for constant function validation.
  std::unordered_map<std::string_view, const ModuleItem*> func_decls_;
  std::unordered_map<std::string_view, std::string_view>
      var_named_types_;  // §11.2.2: var name → named type for aggregate checks
  std::set<std::pair<std::string_view, std::string_view>>
      alias_pairs_;  // §10.11: ordered (min,max) net name pairs already aliased

  // §23.2.2.1: Non-ANSI port declaration tracking.
  std::unordered_set<std::string_view> non_ansi_complete_ports_;
  std::unordered_map<std::string_view, uint32_t> non_ansi_partial_ports_;

  std::unordered_set<std::string_view> ansi_port_names_;

  std::unordered_map<std::string_view, std::string_view> interface_inst_types_;
  // §25.9: virtual interface variable name -> interface type name.
  std::unordered_map<std::string_view, std::string_view> vi_var_interface_types_;
  // §25.9: virtual interface variable name -> selected modport name (or empty).
  std::unordered_map<std::string_view, std::string_view> vi_var_modports_;
  std::unordered_set<std::string_view> checker_inst_names_;
  std::unordered_set<std::string_view> program_inst_names_;  // §24.3
  std::unordered_set<std::string_view> auto_task_func_names_;
  std::unordered_map<std::string_view, ModuleDecl*> nested_module_decls_;

  // §26.3: package → set of names that package provides (built lazily).
  std::unordered_map<std::string_view,
                     std::unordered_set<std::string_view>> pkg_provided_names_;
  // §26.3: per-module explicit imports: name → (package, loc).
  std::unordered_map<std::string_view,
                     std::pair<std::string_view, SourceLoc>> explicit_imports_;
  // §26.3: per-module wildcard-imported package names, in order.
  std::vector<std::string_view> wildcard_packages_;
  // §26.3: per-module names claimed by a reference through a wildcard import.
  std::unordered_map<std::string_view, SourceLoc> wildcard_claimed_;

  // §14.3: Clocking block signal directions for clockvar access validation.
  struct ClockingSignalInfo {
    Direction direction;
  };
  std::unordered_map<std::string_view,
                     std::unordered_map<std::string_view, ClockingSignalInfo>>
      clocking_signals_;  // block_name → (signal_name → info)

  // §23.10.4.1: generate constructs encountered during step (b) hierarchy
  // expansion are enqueued here and evaluated in step (c).
  struct PendingGenerate {
    ModuleItem* item;
    RtlirModule* mod;
  };
  std::vector<PendingGenerate> pending_generates_;

  // §23.10.4.1: defparam assignments that have been applied; used to
  // defer unresolvable targets across iterations and to emit warnings
  // for those that never resolve.
  std::set<std::tuple<RtlirModule*, const ModuleItem*, size_t>>
      applied_defparams_;

  // §23.10.4.2: snapshot of each defparam path's early-resolved target so
  // we can detect bindings that change after the hierarchy is complete.
  struct EarlyDefparamResolution {
    RtlirModule* root;
    const Expr* path_expr;
    RtlirParamDecl* resolved;
    SourceLoc loc;
  };
  std::vector<EarlyDefparamResolution> early_defparam_resolutions_;
};

// Free functions shared across elaborator translation units.
struct ResolvedAttribute;
enum class RtlirProcessKind : uint8_t;

std::vector<ResolvedAttribute> ResolveAttributes(
    const std::vector<Attribute>& attrs, DiagEngine& diag);
uint32_t LookupLhsWidth(const Expr* lhs, const RtlirModule* mod);
RtlirProcessKind MapAlwaysKind(AlwaysKind ak);
void AddProcess(
    RtlirProcessKind kind, ModuleItem* item, RtlirModule* mod, Arena& arena,
    DiagEngine& diag,
    const std::unordered_map<std::string_view, const ModuleItem*>* func_map =
        nullptr);

void ElaborateGateInst(ModuleItem* item, RtlirModule* mod, Arena& arena);

// §28.8: Diagnose connection rules unique to bidirectional pass switches —
// the resistive variants' scalar/bit-select restriction and the UDNT-mixing
// prohibition. No-op for non-bidirectional gate kinds.
void ValidateBidirectionalSwitchConnections(const ModuleItem* item,
                                            const RtlirModule* mod,
                                            DiagEngine& diag);

// §23.10: capture declared type/range info on a value-parameter decl.
void PopulateParamTypeInfo(RtlirParamDecl& pd, const DataType& dtype);

// §23.10.3: capture declared type/range info using a typedef map and scope
// so that ranges which depend on earlier parameters resolve correctly.
void PopulateParamTypeInfo(RtlirParamDecl& pd, const DataType& dtype,
                           const TypedefMap& typedefs, const ScopeMap& scope);

// §23.10: convert an override value to the parameter's declared type/range.
int64_t ConvertOverrideValue(int64_t value, const RtlirParamDecl& pd);

// Shared validation helpers.
std::string_view ExprIdent(const Expr* e);
const ClassDecl* FindClassDecl(std::string_view name,
                               const CompilationUnit* unit);
bool IsRealType(DataTypeKind k);

}  // namespace delta
