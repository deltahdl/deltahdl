#pragma once

#include <string_view>
#include <vector>

namespace delta {

// Forward declarations
class Arena;
class DiagEngine;
struct CompilationUnit;
struct ModuleDecl;
struct RtlirDesign;
struct RtlirModule;
struct Expr;

/// Elaborator transforms a parsed AST (CompilationUnit) into the
/// elaborated RTLIR representation.  Phase 1 supports single-module
/// designs without parameterized instantiation.
class Elaborator {
  public:
    Elaborator(Arena& arena, DiagEngine& diag, CompilationUnit* unit);

    /// Elaborate the design rooted at the given top module.
    /// Returns nullptr on failure (diagnostics emitted via DiagEngine).
    RtlirDesign* elaborate(std::string_view top_module_name);

  private:
    /// Find a module declaration by name in the compilation unit.
    ModuleDecl* find_module(std::string_view name) const;

    /// Elaborate a single module declaration into an RtlirModule.
    using ParamList = std::vector<std::pair<std::string_view, int64_t>>;
    RtlirModule* elaborate_module(ModuleDecl* decl, const ParamList& params);

    /// Populate ports from module declaration port list.
    void elaborate_ports(ModuleDecl* decl, RtlirModule* mod);

    /// Walk module items and populate nets, vars, assigns, processes.
    void elaborate_items(ModuleDecl* decl, RtlirModule* mod);

    Arena& arena_;
    DiagEngine& diag_;
    CompilationUnit* unit_;
};

} // namespace delta
