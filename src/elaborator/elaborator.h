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
#include "elaborator/elaborator_bind_scope.h"
#include "elaborator/elaborator_data.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_operations.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

struct ClassScope;

class Arena;
class DiagEngine;
struct Expr;
struct RtlirDesign;
struct RtlirModule;
struct RtlirVariable;
struct RtlirModuleInst;
struct RtlirParamDecl;

class Elaborator : public ElaboratorOperationRules {
 public:
  // §23.10.2: a module instance parameter value assignment "supplies values for
  // particular instances of a module to any parameters that have been specified
  // in the definition of that module", and this is what one override is worth
  // between the fold that reads it and the RtlirParamDecl that receives it.
  //
  // The value is carried twice because one form of it cannot express the other.
  // `value` is the §11.10 packed number, which is what every integral parameter
  // reads and what ConvertOverrideValue coerces to the declared width.
  // `value_expr` is the expression that number was folded from, which is what a
  // parameter declared string needs: §6.16 gives such a parameter a value of
  // arbitrary length, and an int64_t holds eight characters of one. Keeping the
  // expression rather than a second folded form lets RecordStringParamValue
  // recover the characters with the ConstEvalString it already calls for a
  // declaration's own initializer, so both ends of the override path spell a
  // string value the same way.
  struct ParamOverride {
    std::string_view name;
    int64_t value = 0;
    const Expr* value_expr = nullptr;
  };

  using ParamList = std::vector<ParamOverride>;

  Elaborator(Arena& arena, DiagEngine& diag, CompilationUnit* unit);

  RtlirDesign* Elaborate(std::string_view top_module_name);

  // Elaborates the design rooted at each of the named modules, in the order
  // named. A caller that already knows which modules are the design's tops
  // says so with this form: the hierarchy is rooted at those modules and at no
  // others, where the empty-name form above instead takes every module no
  // instance names for a top (§23.3.1). A name repeated in the list roots one
  // hierarchy rather than two. Naming no module at all elaborates nothing and
  // is reported, since the caller meant to name some.
  RtlirDesign* Elaborate(const std::vector<std::string_view>& top_names);

  RtlirDesign* Elaborate(const ConfigDecl* cfg);

  void SetLibraryDeclarationOrder(std::vector<std::string> order);

  // Sets how many times a loop generate scheme may iterate before elaboration
  // stops and reports. §27.4 states no such bound, so this is a budget: raise
  // it for a design that legitimately generates more instances than
  // kDefaultMaxGenerateIterations admits, and lower it to cap what elaborating
  // a suspect source costs. A value of zero or less reports on the first
  // iteration, which is not a use this has.
  void SetMaxGenerateIterations(int64_t max_iterations);

 private:
  friend struct ItemElaborationStateSaver;  // per-module state save/restore

  void RunPreElaborationValidations();

  // Clause 8 and Clause 18: the checks over the class declarations of the
  // compilation unit, run as one step of RunPreElaborationValidations and in
  // the position it calls them from.
  void RunPreElaborationClassValidations();

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

  // §33.4: the three kinds of binding a config's rules record before its tops
  // are elaborated -- per-instance parameter overrides, cell-clause use and
  // liblist selections, and per-instance plain use bindings.
  void CollectConfigInstanceParamOverrides(const ConfigDecl* cfg);
  void CollectConfigCellClauseOverrides(const ConfigDecl* cfg);
  void CollectConfigInstanceBindOverrides(const ConfigDecl* cfg);

  void ValidateAnonymousProgramNameSharing();

  void ValidateAnonymousProgramHierRefs();

  void ValidatePackageItems();

  void ValidatePackageReferences();

  void ValidatePackageExports();

  void ValidatePackageImportRules(const ModuleDecl* decl);

  void ValidateHierRefToImportedName(const ModuleDecl* decl,
                                     const RtlirModule* mod);

  void ApplyHeaderImports(const ModuleDecl* decl);

  void ApplyBodyImport(const ImportItem& import_item);

  void ValidateModports();

  void ValidateSpecifyBlocks();

  void RegisterCuScopeItems();

  void ResolveExternModules();

  ModuleDecl* FindModule(std::string_view name) const;

  // §33.2.2: a design statement names the top-level cell of the design and, in
  // the library qualifying that name, the source description the cell is taken
  // from. `qualified_in_source` says the configuration's own text named that
  // library, and such a name is looked up in that library alone: a like-named
  // cell held elsewhere is not the description the statement asked for. A
  // library the statement instead inherited from the configuration holding it
  // (§33.4.1.1) is where the search starts rather than where it ends, and an
  // empty `library` confines the search not at all. Returns nullptr when no
  // such cell exists.
  ModuleDecl* FindDesignCell(std::string_view library, std::string_view cell,
                             bool qualified_in_source) const;

  // Applies a cell selection clause's use expansion to a cell being resolved
  // (§33.4.1.4, §33.4.1.6). Returns nullopt when no clause applies (resolution
  // should continue normally); a present value (possibly nullptr) is the bound
  // cell, where nullptr means the named target does not exist.
  std::optional<ModuleDecl*> ResolveCellUseOverride(
      std::string_view name) const;

  // Applies an instance selection clause's plain use expansion to the instance
  // currently being resolved (§33.4.1.6). The exact instance at the named path
  // is bound to the specified library.cell, independent of the instance's
  // declared cell name; an omitted library is inherited from the parent cell.
  // Returns nullopt when no clause applies; a present value (possibly nullptr)
  // is the bound cell, where nullptr means the named target does not exist.
  std::optional<ModuleDecl*> ResolveInstanceBindOverride() const;

  ModuleDecl* FindModuleInScope(std::string_view name) const;

  // §6.18: reports a declaration the parser recorded as two bare identifiers
  // and a semicolon whose first name it had not yet seen declared as a type.
  // The shape is a data declaration whose type_identifier breaches "The
  // declaration of a user-defined data type shall precede any reference to its
  // type_identifier" and a module instantiation missing its port connection
  // list both, and which of the two it is turns on whether the name is a
  // module, which the parser does not know and this does.
  void ReportUndeclaredTypeName(const ModuleItem* item);

  RtlirModule* ElaborateModule(const ModuleDecl* decl, const ParamList& params);

  // §6.20.2: resolves each parameter of `decl`'s parameter port list against
  // `params`, the overrides the instantiation supplied, and appends the result
  // to mod->params. Each is resolved against a scope rebuilt from the
  // parameters already appended, so one parameter port may be written in terms
  // of an earlier one.
  void ElaborateParamPortList(const ModuleDecl* decl, const ParamList& params,
                              RtlirModule* mod);

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

  void ElaborateSequenceDeclItem(ModuleItem* item, RtlirModule* mod);
  void ElaboratePropertyDeclItem(ModuleItem* item, RtlirModule* mod);
  void CheckPropertyOperandInstances(const ModuleItem* item);
  void ElaborateAssertPropertyItem(ModuleItem* item, RtlirModule* mod);
  void ElaborateParamDecl(ModuleItem* item, RtlirModule* mod);
  void ElaborateNetDecl(ModuleItem* item, RtlirModule* mod);
  // §6.6.7: elaborates a declaration whose named data type is a user-defined
  // nettype as the net it declares, answering true when it was one. A nettype
  // name reaches ElaborateVarDecl because the parser reads `mynet w;` as a
  // variable declaration of a named type, and it is here rather than there to
  // keep that function inside the statement count clang-tidy holds it to.
  bool ElaborateUserNettypeNet(ModuleItem* item, RtlirModule* mod);

  void ElaborateVarDecl(ModuleItem* item, RtlirModule* mod);
  // §23.2.2.1: reconciles the signedness of a non-ANSI port with its separate
  // net or variable declaration -- `signed` on either side makes both signed.
  // Returns the reconciled signedness for the net/variable declaration.
  bool ReconcilePartialPortSignedness(std::string_view name, bool decl_signed,
                                      RtlirModule* mod);
  void SetVariableTypeInfo(const ModuleItem* item, RtlirVariable& var);
  void ElaborateContAssign(ModuleItem* item, RtlirModule* mod);
  void ValidateContAssignIdentLhs(ModuleItem* item, RtlirModule* mod);
  void ValidateContAssignNettypeAndDelay(ModuleItem* item);
  void ValidateContAssignDriveStrength(ModuleItem* item, RtlirModule* mod);
  void ElaborateSpecparam(ModuleItem* item, RtlirModule* mod);

  void ElaborateTypedef(ModuleItem* item, RtlirModule* mod);
  void ValidateTypedefShape(const DataType& dtype, SourceLoc loc,
                            const ScopeMap* member_default_scope);
  void ValidateCuTypedefs();

  void ElaborateNettypeDecl(ModuleItem* item, RtlirModule* mod);
  void RegisterNettypeResolutionAndCanonical(const ModuleItem* item);
  // §6.6.7: a named resolution function shall return the nettype's data type
  // and take a single input argument that is a dynamic array of that type.
  void CheckNettypeResolutionFunction(const ModuleItem* item);

  void ElaborateItems(const ModuleDecl* decl, RtlirModule* mod);

  // §23.4: a nested design element with no ports and no un-defaulted parameter
  // port is implicitly instantiated once inside its enclosing element, unless
  // the source instantiated it explicitly.
  void InstantiateImplicitNestedModules(
      const std::vector<std::pair<std::string_view, ModuleDecl*>>& nested,
      RtlirModule* mod);
  // Clears every per-module bookkeeping table before a module's items are
  // elaborated, and runs the post-item legality validations for `decl`/`mod`.
  void ResetItemElaborationState();
  void RunPostItemValidations(const ModuleDecl* decl, RtlirModule* mod);

  void ElaborateModuleInst(ModuleItem* item, RtlirModule* mod);

  // Reports a gate or user-defined primitive instance whose terminals are the
  // wrong width, under whichever of the two rules the instance is held to.
  // §28.3.6 rules the terminal of an instance array, whose bit-length shall be
  // either one or the instance-array length. §4.9.6 rules the output or inout
  // terminal of a single instance, which "shall be connected directly to 1-bit
  // nets or 1-bit structural net expressions". Both kinds of instance ask this
  // together because §29.8 puts them under one rule: a user-defined primitive
  // instance connects its terminals by "the terminal connection rules ...
  // outlined in 28.3.6", the rules a gate instance connects by, and §4.9.6
  // states its rule of "Primitive terminals, including UDP terminals".
  void CheckInstanceTerminalWidths(const ModuleItem* item,
                                   const RtlirModule* mod);

  // §29.8: records on `mod` every instance of a user-defined primitive that one
  // instantiation writes, so that the primitive drives the nets its output
  // terminals name. An instantiation written with the optional range §29.8
  // admits is one instance per array element.
  void ElaborateUdpInst(ModuleItem* item, RtlirModule* mod);

  // §29.8: appends the one instance of a user-defined primitive that the
  // terminal list currently held on `item` describes.
  void ElaborateOneUdpInst(const ModuleItem* item, RtlirModule* mod);

  UdpDecl* FindUdpByName(std::string_view name) const;

  // §33.4.1.4/§33.4.1.6: applies a cell selection clause's use expansion to a
  // primitive being resolved. Returns nullopt when no clause applies (the
  // library search should run); a present value (possibly nullptr) is the bound
  // primitive, where nullptr means the named target does not exist.
  std::optional<UdpDecl*> ResolveUdpUseOverride(std::string_view name) const;

  void ReclassifyForwardUdpInstances(const ModuleDecl* decl);

  Expr* MakePullExpr(NetType drive);
  Expr* MakeHighZExpr();

  void BindPorts(RtlirModuleInst& inst, const ModuleItem* item,
                 RtlirModule* parent_mod, const ModuleDecl* child_decl);

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
  // §23.3.3.2: records every variable an output or inout port connection
  // drives, so a second output driving the same variable is rejected.
  void RecordOutputPortDrivenVariables(const Expr* conn_expr, SourceLoc loc);
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

  // §23.9: the resolved parameters of `mod` as a scope, holding those a
  // reference standing in the generate blocks `scopes` can see -- the prefixes
  // in force at that reference, outermost first, empty for a reference among
  // the module's own items. A parameter one generate block declares is not
  // visible at module level or in a sibling block, so passing the wrong list
  // folds a constant expression against a declaration it cannot name.
  ScopeMap BuildParamScope(const RtlirModule* mod,
                           const std::vector<std::string_view>& scopes) const;

  // The same for a reference standing where this elaboration is, which is what
  // every site inside the module being elaborated wants.
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

  // §27.5: elaborate the one generate block a conditional generate construct
  // selected, opening the scope that block creates. `block_name` is the name
  // the block carries, which §27.6 has already supplied where the source wrote
  // none, and `has_begin_end` says whether the block was written with the
  // `begin` and `end` keywords, which decides whether it is directly nested.
  // §27.5: one generate block of a conditional generate construct, which the
  // construct "selects at most one of" and this elaborates. The then-branch,
  // each case item and the final else are the same entity written three ways,
  // and ModuleItem and GenerateCaseItem spell its name under different member
  // names, so the four call sites assemble one of these rather than the node.
  //
  // `name_is_generated` says §27.6 assigned `name` rather than the source
  // writing it, which §23.6 makes the difference between a block a
  // hierarchical name can reach into and one it cannot.
  struct ConditionalGenerateBlock {
    std::string_view name;
    bool name_is_generated = false;
    const std::vector<ModuleItem*>& body;
    bool has_begin_end = false;
  };

  void ElaborateConditionalGenerateBlock(const ConditionalGenerateBlock& block,
                                         RtlirModule* mod,
                                         const ScopeMap& scope);

  // §27.4: a loop generate construct's genvar, once its header has been
  // checked -- the genvar name and the constant value its control variable
  // starts at.
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

  void ElaborateGenerateItems(const std::vector<ModuleItem*>& items,
                              RtlirModule* mod, const ScopeMap& scope);

  void AssignGenerateBlockNames(const ModuleDecl* decl);

  void CheckConditionalGenerateNaming(const ModuleDecl* decl);

  // Every defparam statement belonging to `mod`: the ones ModuleDecl::items
  // holds directly, then the ones each generate block instance elaborated into
  // `mod` contributed. Elaborator::ApplyDefparams and
  // Elaborator::ReportUnresolvedDefparams both read this one list, so the keys
  // they build out of it agree and a statement one applied is not one the other
  // reports as having reached nothing.
  std::vector<DefparamSite> CollectDefparamSites(RtlirModule* mod,
                                                 const ModuleDecl* decl) const;

  void ApplyDefparams(RtlirModule* mod, const ModuleDecl* decl);

  void ApplyDefparamSite(RtlirModule* mod, const DefparamSite& site,
                         const ScopeMap& scope);

  void ApplyDefparamsRecursively(RtlirModule* mod);

  void WarnUnresolvedDefparams(RtlirModule* mod);

  void ReportUnresolvedDefparams(RtlirModule* mod, const ModuleDecl* decl);

  void ReportUnresolvedDefparamSite(RtlirModule* mod, const DefparamSite& site,
                                    const ScopeMap& mod_scope);

  void VerifyEarlyResolvedDefparams();

  void CheckEarlyResolutionAmbiguity(
      RtlirModule* mod, const std::unordered_set<std::string_view>& top_names);

  void ProcessPendingGenerate(const PendingGenerate& pg);

  // Resolves a §23.6 hierarchical path, already read into steps, against the
  // instances elaborated under `root`. `writer` is the generate block instance
  // the defparam statement stands in, and the path starts there: §23.10.1
  // rules that a defparam "in or under a generate block instance shall not
  // change a parameter value outside that hierarchy", and a path that reaches
  // outside is one no sequence of steps from `writer` arrives at, so the rule
  // holds by construction rather than by a check that could be skipped.
  RtlirParamDecl* ResolveDefparamSteps(RtlirModule* root, const HierPath& path,
                                       const HierPath& writer,
                                       RtlirModule** out_mod = nullptr);

  void RecomputeDependentParams(RtlirModule* mod);

  bool MaybeCreateImplicitNet(std::string_view name, SourceLoc loc,
                              RtlirModule* mod);

  std::string_view ScopedName(std::string_view base);
  // The generate prefix currently in force, arena-persisted so it outlives the
  // mutable member it is copied from. Empty outside any generate construct.
  std::string_view InternedGenPrefix();

  void ResolveTypeRef(ModuleItem* item, const RtlirModule* mod);

  void ValidateArrayInitPattern(const ModuleItem* item);
  void ValidateStructInitPattern(const ModuleItem* item);

  void ValidateModuleConstraints(const ModuleDecl* decl, RtlirModule* mod);

  void ValidateTimescaleConsistency();

  void ValidateStandaloneTimescaleOrder();

  void ValidateEnumDecl(const DataType& dtype, SourceLoc loc,
                        bool declares_its_constants);

  void ValidatePackedStructDefaults(const DataType& dtype, SourceLoc loc);
  void ValidateUnpackedStructWithUnionDefaults(const DataType& dtype,
                                               SourceLoc loc);
  void ValidateStructMemberDefaultsConstant(const DataType& dtype,
                                            SourceLoc loc,
                                            const ScopeMap& scope);

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

  void TrackVarArrayInfo(
      const ModuleItem* item, RtlirVariable& var, const ScopeMap& scope,
      std::unordered_map<std::string_view, VarArrayInfo>& out);
  void RecordNetArrayShape(ModuleItem* item, const RtlirNet& net,
                           RtlirModule* mod);

  void ValidateVarDeclTypes(ModuleItem* item, const ScopeMap& scope);

  bool ValidateEnumLiteral(const EnumMember& member, uint32_t base_width,
                           bool is_2state);

  void ValidateEdgeOnReal(const ModuleItem* item);

  void ValidateItemConstraints(const ModuleItem* item, const ScopeMap& scope);

  void ValidateDeferredAssertionActions(const ModuleDecl* decl);
  void WalkStmtsForDeferredActions(
      const Stmt* s, const std::unordered_set<std::string_view>& auto_vars);

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
  void ValidateStringOutputTaskTargets(const ModuleDecl* decl);
  void ValidatePlaAscendingOrder(const ModuleDecl* decl);
  void ValidateBitsCallRestrictions(const ModuleDecl* decl);
  void ValidateBitVectorFunctionArgs(const ModuleDecl* decl);

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
  //
  // Both walk each module declaration, each package body and the
  // compilation-unit items, because A.1.11 makes a DPI import or export a
  // package_item and each of the three is one scope for the rules stated over
  // declarations "in the same scope".
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

  // §18.17 — a production identifier is local to the scope its randsequence
  // statement creates, so every one the statement writes shall name one of
  // that statement's own productions.
  void ValidateRandsequenceProductionNames(const ModuleDecl* decl);

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

  // §15.4.9: the compile-time type check a parameterized mailbox applies to the
  // arguments of its put/get/peek (and try_ variants) methods.
  void ValidateParameterizedMailboxCalls(const ModuleDecl* decl);

  void ValidateArrayArgTypes(const ModuleDecl* decl);

  void TrackEnumVariable(const ModuleItem* item);
  // Declares the named constants of an enumeration written directly in a data
  // declaration rather than in a typedef (§6.19, Syntax 6-5), giving each the
  // value it takes so a read of the name finds it.
  void EmitBareEnumMembers(const ModuleItem* item, RtlirModule* mod);

  void ValidateEnumAssignments(const ModuleDecl* decl);

  void WalkStmtsForEnumAssign(const Stmt* s);

  void ValidateConstAssignments(const ModuleDecl* decl);

  void WalkStmtsForConstAssign(const Stmt* s);

  // §6.20: reports a procedural write whose left-hand side reaches a constant,
  // naming the constant it reaches. `loc` is where the assignment stands, since
  // that is what somebody whose source was rejected has to find.
  void ReportConstAssignTarget(const Expr* lhs, SourceLoc loc);

  // §6.20: the same report for a call statement that writes its object, which
  // §6.16 gives six of the string methods. A call is not an assignment and no
  // lvalue walk reaches it, so it is asked about separately and answered the
  // same way, the object being what ReportConstAssignTarget is handed.
  void ReportConstMutatingMethodCall(const Expr* call, SourceLoc loc);

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

  void DefaultPackageTaskFuncLifetimes();
  void ValidatePackageValueParams();

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
  void ValidateSuperRules();

  void ValidateOutOfBlockDeclarations();

  void ValidateParameterizedScopeResolution(const ModuleDecl* decl);

  // §8.23: an incomplete forward type, a type defined by an interface-based
  // typedef (§6.18) and a type parameter (§6.20.3) may prefix the class scope
  // resolution operator only in a typedef declaration, the type operator, or a
  // type parameter assignment, never in an ordinary expression.
  void ValidateRestrictedScopePrefixUsage(const ModuleDecl* decl);

  // §6.20.3: the same restriction over the body of a class declared at the
  // outermost level, whose enclosing scope is the compilation unit. This is the
  // position the subclause writes its own example in, `C::T x;` in the body of
  // `class P#(type C)`.
  void ValidateRestrictedScopePrefixInClasses();

  // §6.20.3: a type parameter used as a class scope resolution prefix shall
  // resolve to a class.
  void ValidateTypeParamScopePrefixResolvesToClass(const ModuleDecl* decl);

  void ValidateInterfaceClassRules();

  void ValidateForwardClassTypedefs();

  void ValidateForwardTypedefsInScope(const ModuleDecl* decl);

  void ValidateForwardTypedefScopePrefix(const ModuleDecl* decl);
  void ValidateInterfaceClassMembers(const ClassDecl* cls);
  void ValidateInterfaceClassInheritance(const ClassDecl* cls,
                                         const ClassScope& scope);
  void ValidateRegularClassInheritance(const ClassDecl* cls,
                                       const ClassScope& scope);
  void ValidateImplementsInterfaceMethods(const ClassDecl* cls);
  void ValidateVirtualClassInterfaceObligations(const ClassDecl* cls,
                                                const ScopeMap& params);
  void ValidateImplementsTypeAccess(const ClassDecl* cls,
                                    const ScopeMap& params);
  void CheckImplementsTypeAccessOfMember(
      const ClassMember* m,
      const std::unordered_map<std::string_view, std::string_view>&
          owning_iface,
      const std::unordered_set<std::string_view>& visible);
  void CheckImplementsTypeAccessOfType(
      const DataType& dt, SourceLoc loc,
      const std::unordered_map<std::string_view, std::string_view>&
          owning_iface,
      const std::unordered_set<std::string_view>& visible);

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
  // §16.15: more than one default disable iff declaration within the same
  // module, interface, or program declaration shall be an error.
  void ValidateDuplicateDefaultDisableIff(const ModuleDecl* decl);
  void ValidateGlobalClockReference(const ModuleDecl* decl);
  // §16.9.4: the global clocking sampled value functions ($past_gclk, …,
  // $changing_gclk) require a global clocking to be defined in scope.
  void ValidateGclkRequiresGlobalClocking(const ModuleDecl* decl);
  // §16.9.4: the global clocking future sampled value functions may appear only
  // in a property or sequence expression, not in procedural code.
  void ValidateFutureGclkPlacement(const ModuleDecl* decl);
  // §14.14: true when `decl` itself contains a global clocking declaration.
  static bool ModuleDeclaresGlobalClocking(const ModuleDecl* decl);
  // §16.5.2: the clocking event of the global clocking declaration `decl`
  // itself contains, or null when it declares none. This is the event a
  // $global_clock leading clocking event stands for.
  static const std::vector<EventExpr>* ModuleGlobalClockingEvent(
      const ModuleDecl* decl);
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

  void ValidateScopeRules(const ModuleDecl* decl);

  // §5.6/§6.5: flags an unresolved bare identifier read on a cont-assign RHS.
  void ValidateUnresolvedReferences(const ModuleDecl* decl,
                                    const RtlirModule* mod);
  bool IsDeclaredNameForRhs(std::string_view name) const;
  // True when `name` resolves against any module-level name set (see .cpp).
  bool IsNameInModuleScope(std::string_view name) const;

  // §23.9/§24.3: snapshot of the names declared in the scope currently being
  // elaborated, captured when descending into a lexically-nested declaration so
  // the nested scope can resolve enclosing-scope identifiers.
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
};

}  // namespace delta
