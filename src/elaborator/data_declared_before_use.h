#pragma once

#include <functional>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"

namespace delta {

// Whether a scope enclosing the one walked makes `name` visible at `use`.
using OuterScopes = std::function<bool(std::string_view name, SourceLoc use)>;

// §6.5 (printed page 91): data shall be declared before it is used, implicit
// nets apart. Reports each bare name that an item of `items` reads, writes in a
// procedure or a subroutine, or names in a declaration's dimensions or value,
// where every scope declaring it as a variable, net or parameter does so only
// further down. The blocks of the generate constructs among `items` are scopes
// nested in it, so a name a block declares is looked for there first.
//
// A continuous assignment's target and the terminals of an instance are left
// out, being where §6.10 declares an implicit net. A class's properties are
// data of its body, and a name one of its bases may declare is passed by;
// `unit` holds the classes a base class can be. `outer` answers whether
// a scope enclosing `items` -- a port list, an import or the compilation unit
// -- makes the name visible, and a use reaching such a declaration is no use
// before its declaration.
void ReportDataUsedAboveItsDeclaration(const std::vector<ModuleItem*>& items,
                                       const CompilationUnit& unit,
                                       const OuterScopes& outer,
                                       DiagEngine& diag);

// The same of each package's items and of the compilation unit's, and of the
// bodies of the classes declared at its scope, each answered with the names
// the scope's own imports may supply.
void ReportDataUsedAboveItsDeclaration(const CompilationUnit& unit,
                                       DiagEngine& diag);

// Whether `decl` names `name` among its ports, or `unit` among its items above
// `use`: the enclosing scopes a module's name reaches without an import.
bool NamedOutsideTheElement(const ModuleDecl* decl, const CompilationUnit* unit,
                            std::string_view name, SourceLoc use);

}  // namespace delta
