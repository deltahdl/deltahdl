#pragma once

#include <vector>

#include "simulator/vpi_object.h"

// The relations of §37.34's constraint, constraint ordering and dist item, and
// of §37.38's constraint if else, that the parts of a constraint serve from
// the fields VpiObject keeps them in.

namespace delta {

// §37.38 (figure): the list a constraint if-else's vpiElseConst relation
// walks, its else branch, and §37.34's: a constraint ordering's vpiSolveBefore
// and vpiSolveAfter lists. Null for any other relation of `ref`.
const std::vector<VpiObject*>* VpiConstraintListOf(int type,
                                                   const VpiObject* ref);

// §37.34: what a constraint's vpiParent reaches, the class obj holding it and
// nothing for a constraint any other object holds, the figure drawing the
// edge from no other holder; the expression a distribution weights, its one
// child no dist item; and a dist item's vpiValueRange and vpiWeight. False,
// leaving `out` alone, for any other relation.
bool VpiTryResolveConstraintRelation(int type, VpiHandle ref, VpiHandle& out);

}  // namespace delta
