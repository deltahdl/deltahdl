#pragma once

#include <vector>

#include "common/diagnostic.h"
#include "elaborator/rtlir.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

// §17.3: the checker instantiations the procedure body `body` holds, each a
// procedural checker instance, in source order.
std::vector<Stmt*> CheckerInstantiationsIn(Stmt* body);

// §17.3: whether the instantiation `item`, standing in a procedure of `mod`,
// is elaborated as a procedural checker instance of `child`, the design
// element it names, or nullptr where it names none, which the elaboration of
// the instance reports. Only a checker may be instantiated in procedural
// code, and not in a procedure of another checker, so either breach is
// reported and refused; a checker's instantiation is held to the form
// A.4.1.4 gives it, as one written as a module item is.
bool AdmitProceduralCheckerInstance(const ModuleItem* item,
                                    const ModuleDecl* child,
                                    const RtlirModule* mod, DiagEngine& diag);

}  // namespace delta
