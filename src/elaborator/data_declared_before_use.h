#pragma once

#include <functional>
#include <string_view>

#include "common/diagnostic.h"
#include "elaborator/rtlir.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"

namespace delta {

// §6.5 (printed page 91): data shall be declared before it is used, implicit
// nets apart. Reports each bare name that an item of `decl` reads, writes in a
// procedure or a subroutine, or names in a declaration's dimensions or value,
// where every scope declaring it as a variable, net or parameter does so only
// further down. The blocks of the generate constructs among the items are
// scopes nested in the element, so a name a block declares is looked for there
// first.
//
// A continuous assignment's target and the terminals of an instance are left
// out, being where §6.10 declares an implicit net. A class's properties are
// data of its body, and a name one of its bases may declare is passed by;
// `unit` holds the classes a base class can be. A name a scope enclosing the
// element makes visible at the use -- a port of `decl`, an import `mod` or the
// unit holds, a declaration of the unit written above the use, or a name
// `enclosing` answers for the module a nested module is declared in -- is no
// use before its declaration.
void ReportDataUsedAboveItsDeclaration(
    const ModuleDecl& decl, const RtlirModule& mod, const CompilationUnit& unit,
    const std::function<bool(std::string_view)>& enclosing, DiagEngine& diag);

// The same of each package's items and of the compilation unit's, and of the
// bodies of the classes declared at its scope, each answered with the names
// the scope's own imports may supply.
void ReportDataUsedAboveItsDeclaration(const CompilationUnit& unit,
                                       DiagEngine& diag);

}  // namespace delta
