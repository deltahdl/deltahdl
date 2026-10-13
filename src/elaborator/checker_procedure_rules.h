#pragma once

#include "common/diagnostic.h"
#include "parser/ast_module.h"

namespace delta {

// §17.6: reports each variable declared in a procedure of the checker `decl`
// whose type is a covergroup the checker declares; a covergroup instance
// belongs in the checker body, never in its procedures. Runs only on checker
// declarations.
void ValidateCheckerProcedureCovergroups(const ModuleDecl* decl,
                                         DiagEngine& diag);

// §17.8 with §16.6: reports each call, on the right-hand side of an
// assignment in a procedure of the checker `decl`, of a function the checker
// declares with an output, inout or non-const ref argument. Runs only on
// checker declarations.
void ValidateCheckerAssignmentCalls(const ModuleDecl* decl, DiagEngine& diag);

// §16.6: whether the function `fn` has an output, inout or non-const ref
// formal, whose actual it writes back; a formal written without a direction
// takes the one before it, the first input (§13.3).
bool HasArgumentWrittenBack(const ModuleItem* fn);

}  // namespace delta
