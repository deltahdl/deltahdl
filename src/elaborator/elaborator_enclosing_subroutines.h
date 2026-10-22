#pragma once

#include <string_view>
#include <unordered_set>
#include <vector>

namespace delta {

struct CompilationUnit;
struct ModuleDecl;
struct ModuleItem;

// Whether `item` declares a task or a function a call may call: one the
// source writes, or one a DPI import or export names (§35.5).
bool IsSubroutineItem(const ModuleItem& item);

// Whether the interface `unit` declares under `iface` declares a task or a
// function `name`.
bool InterfaceDeclaresSubroutine(const CompilationUnit& unit,
                                 std::string_view iface, std::string_view name);

// §23.8: the tasks and functions the modules of `unit` that instantiate
// `module`, directly or through instances between, declare, which a call the
// module writes by a name it does not declare may name.
std::unordered_set<std::string_view> EnclosingSubroutineNames(
    const CompilationUnit& unit, std::string_view module);

// §26.3 with §24.3: the package imports a reference written in `decl` reaches
// once its search leaves `decl` for the scopes lexically enclosing it, where
// `decl` is declared within another module, interface or program, each list
// holding the innermost scope's first.
struct EnclosingImports {
  // Those each enclosing scope writes before the declaration nesting `decl`,
  // which every reference reaches.
  std::vector<ModuleItem*> above;
  // The explicit imports each writes after it, which a task or function call
  // reaches as well, its search taking a scope's locally visible identifiers
  // to the end of the scope.
  std::vector<ModuleItem*> explicit_below;
};

// The imports of the scopes enclosing `decl`; both lists empty for a
// declaration nested in none.
EnclosingImports EnclosingImportsOf(const CompilationUnit& unit,
                                    const ModuleDecl& decl);

}  // namespace delta
