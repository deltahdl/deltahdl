#pragma once

#include <string_view>
#include <unordered_set>

#include "parser/ast_module.h"

namespace delta {

struct CompilationUnit;

void AddImportedData(const CompilationUnit& unit, const ImportItem& import,
                     std::unordered_set<std::string_view>& names);

std::unordered_set<std::string_view> PackageReferencedNames(
    const PackageDecl* pkg);

}  // namespace delta
