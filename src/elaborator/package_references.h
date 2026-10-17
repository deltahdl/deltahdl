#pragma once

#include <string_view>
#include <unordered_set>

#include "parser/ast_module.h"

namespace delta {

struct CompilationUnit;

// §26.3: the variables and nets the package `import` names brings in, by its
// item name or with a wildcard, added to `names`.
void AddImportedData(const CompilationUnit& unit, const ImportItem& import,
                     std::unordered_set<std::string_view>& names);

// §26.6 (printed page 815) with §26.3 (printed 810): the names the package
// `pkg`'s own declarations write, in their expressions and as the names of
// types, which are the candidates of its wildcard imports it actually imports
// and so hands on through a wildcard export. Taken generously: a name written
// anywhere in the package counts, a declaration's own name and a member's
// after a dot among them, so no candidate the package reads is missed.
std::unordered_set<std::string_view> PackageReferencedNames(
    const PackageDecl* pkg);

}  // namespace delta
