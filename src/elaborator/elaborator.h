#pragma once

#include <cstdint>
#include <string>
#include <string_view>
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

 private:
  /// §3.13: Check definitions and package name spaces for duplicates.
  void ValidateNameSpaces();

  /// §3.12.1: Register CU-scope typedefs/classes before module elaboration.
  void RegisterCuScopeItems();

  /// Find a module declaration by name in the compilation unit.
  ModuleDecl* FindModule(std::string_view name) const;

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

  /// Create a pull0/pull1 constant expression for §22.9.
  Expr* MakePullExpr(NetType drive);

  /// Bind instance ports to continuous assignments.
  void BindPorts(RtlirModuleInst& inst, const ModuleItem* item,
                 RtlirModule* parent_mod);

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

  /// Apply defparam overrides after hierarchy is built.
  void ApplyDefparams(RtlirModule* top, const ModuleDecl* decl);

  /// Resolve a hierarchical path to find the target module and param name.
  RtlirParamDecl* ResolveDefparamPath(RtlirModule* root, const Expr* path_expr);

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

  /// §10.2 Table 10-1: Continuous assignment LHS selects must be constant.
  void ValidateContAssignConstSelect(const ModuleDecl* decl);

  /// §A.1.4: Validate elaboration severity system task (finish_number).
  void ValidateElabSystemTask(const ModuleItem* item);

  /// §10.11: Validate alias statement operands.
  void ValidateAlias(const ModuleItem* item);

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

  /// §3.12.1: Find a CU-scope item by name.
  ModuleItem* FindCuScopeItem(std::string_view name) const;

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
    bool is_dynamic = false;
    bool is_assoc = false;
    std::string_view assoc_index_type;  // §7.9.9: e.g. "int", "string", "*"
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

  // §14.3: Clocking block signal directions for clockvar access validation.
  struct ClockingSignalInfo {
    Direction direction;
  };
  std::unordered_map<std::string_view,
                     std::unordered_map<std::string_view, ClockingSignalInfo>>
      clocking_signals_;  // block_name → (signal_name → info)
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

// Shared validation helpers.
std::string_view ExprIdent(const Expr* e);
const ClassDecl* FindClassDecl(std::string_view name,
                               const CompilationUnit* unit);
bool IsRealType(DataTypeKind k);

}  // namespace delta
