#pragma once

#include <string_view>
#include <unordered_set>
#include <vector>

namespace delta {

struct CompilationUnit;
struct ModuleDecl;
struct ModuleItem;

bool IsSubroutineItem(const ModuleItem& item);

bool InterfaceDeclaresSubroutine(const CompilationUnit& unit,
                                 std::string_view iface, std::string_view name);

std::unordered_set<std::string_view> EnclosingSubroutineNames(
    const CompilationUnit& unit, std::string_view module);

struct EnclosingImports {
  std::vector<ModuleItem*> above;
  std::vector<ModuleItem*> explicit_below;
};

EnclosingImports EnclosingImportsOf(const CompilationUnit& unit,
                                    const ModuleDecl& decl);

}  // namespace delta
