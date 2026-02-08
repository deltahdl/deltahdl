#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

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

  /// Elaborate a typedef item (e.g. enum constants).
  void ElaborateTypedef(ModuleItem* item, RtlirModule* mod);

  /// Walk module items and populate nets, vars, assigns, processes.
  void ElaborateItems(const ModuleDecl* decl, RtlirModule* mod);

  /// Elaborate a module instantiation (resolve child, bind ports).
  void ElaborateModuleInst(ModuleItem* item, RtlirModule* mod);

  /// Bind instance ports to continuous assignments.
  void BindPorts(RtlirModuleInst& inst, const ModuleItem* item);

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

  /// Return a scoped name (prefixed during generate-for expansion).
  std::string_view ScopedName(std::string_view base);

  Arena& arena_;
  DiagEngine& diag_;
  CompilationUnit* unit_;
  std::string gen_prefix_;
  TypedefMap typedefs_;
};

}  // namespace delta
