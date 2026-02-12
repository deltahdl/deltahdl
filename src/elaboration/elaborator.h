#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/source_loc.h"
#include "elaboration/const_eval.h"
#include "elaboration/type_eval.h"

namespace delta {

// Forward declarations
class Arena;
class DiagEngine;
struct CompilationUnit;
struct ModuleDecl;
struct RtlirDesign;
struct RtlirModule;
struct ModuleItem;
struct Expr;
struct RtlirModuleInst;
struct RtlirParamDecl;
struct EnumMember;
struct Stmt;

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
  void ElaborateContAssign(ModuleItem* item, RtlirModule* mod);
  void ElaborateSpecparam(ModuleItem* item, RtlirModule* mod);

  /// Elaborate a typedef item (e.g. enum constants).
  void ElaborateTypedef(ModuleItem* item, RtlirModule* mod);

  /// §6.6.7: Elaborate a nettype declaration.
  void ElaborateNettypeDecl(ModuleItem* item, RtlirModule* mod);

  /// Walk module items and populate nets, vars, assigns, processes.
  void ElaborateItems(const ModuleDecl* decl, RtlirModule* mod);

  /// Elaborate a module instantiation (resolve child, bind ports).
  void ElaborateModuleInst(ModuleItem* item, RtlirModule* mod);

  /// Bind instance ports to continuous assignments.
  void BindPorts(RtlirModuleInst& inst, const ModuleItem* item,
                 RtlirModule* parent_mod);

  /// Build a scope map from resolved module parameters.
  static ScopeMap BuildParamScope(const RtlirModule* mod);

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

  /// Validate array assignment pattern element count (§5.11).
  void ValidateArrayInitPattern(const ModuleItem* item);

  /// Run all post-item validation checks for a module (§6).
  void ValidateModuleConstraints(const ModuleDecl* decl);

  /// Validate enum declaration constraints (§6.19).
  void ValidateEnumDecl(const DataType& dtype, SourceLoc loc);

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

  /// §6.6.8: interconnect net cannot appear in continuous assignment.
  void ValidateInterconnectContAssign(const ModuleItem* item);

  /// Check for mixed continuous/procedural assignments (§6.5).
  void ValidateMixedAssignments();

  /// Check specparam not used in parameter expressions (§6.20.5).
  void ValidateSpecparamInParams(const ModuleDecl* decl);

  /// §13.4.1: Validate void function doesn't return a value.
  /// §13.4.4: Validate only fork/join_none in function body.
  void ValidateFunctionBody(const ModuleItem* item);

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

  Arena& arena_;
  DiagEngine& diag_;
  CompilationUnit* unit_;
  std::string gen_prefix_;
  TypedefMap typedefs_;

  // Per-module validation state (cleared in ElaborateItems).
  std::unordered_set<std::string_view> declared_names_;
  std::unordered_map<std::string_view, SourceLoc> cont_assign_targets_;
  std::unordered_set<std::string_view> proc_assign_targets_;
  std::unordered_map<std::string_view, DataTypeKind> var_types_;
  std::unordered_set<std::string_view> specparam_names_;
  std::unordered_set<std::string_view> enum_var_names_;
  std::unordered_set<std::string_view> enum_member_names_;
  std::unordered_set<std::string_view> const_names_;    // §6.20.6: const vars
  std::unordered_set<std::string_view> class_names_;    // §8: known class names
  std::unordered_set<std::string_view> nettype_names_;  // §6.6.7: nettypes
  std::unordered_set<std::string_view> interconnect_names_;  // §6.6.8
};

}  // namespace delta
