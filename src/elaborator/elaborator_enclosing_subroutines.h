#pragma once

#include <string_view>
#include <unordered_set>

namespace delta {

struct CompilationUnit;
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

}  // namespace delta
