#pragma once

#include <string_view>
#include <unordered_map>

#include "common/diagnostic.h"
#include "parser/ast_type.h"

namespace delta {

struct ModuleDecl;

// A.2.5 with §7.4.2: an unpacked dimension's bounds, and a queue dimension's,
// are constant expressions, and a variable or a net is none (§11.2.1), a const
// variable included, being set at run time (§6.20.6). Reports each of the
// module's variables and nets, the names of `values`, that a net or variable
// declaration of the module `decl` reads in one of its unpacked dimensions,
// written at module scope, in a procedural block or in a task or function. A
// name a block or a subroutine declares again is left alone, and nothing inside
// a call, a member select or a type reference is read, `$size(v)` of a
// fixed-size array being a constant.
void CheckVariableReadsInUnpackedDims(
    const ModuleDecl* decl,
    const std::unordered_map<std::string_view, DataTypeKind>& values,
    DiagEngine& diag);

}  // namespace delta
