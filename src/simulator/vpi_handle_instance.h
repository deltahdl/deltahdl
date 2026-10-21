#pragma once

#include "simulator/vpi_object.h"

namespace delta {

// §37.10 detail 3: vpi_handle(vpiInstance, obj) resolves to the immediate
// enclosing instance - the nearest package, module, interface, or program the
// object is instantiated in. The relation is not stored as a designated pointer
// on the object; it is derived by walking outward through the scope chain, so
// vpi_handle() resolves it here rather than by its generic single-level
// parent/child walk, which would miss any intervening non-instance scope such
// as a named begin block. A null result is the correct answer when no instance
// encloses the object, so this always claims the relation. Detail 2's
// vpiModule is derived the same way: the module the object is inside, through
// a begin block, a generate scope or an interface or program instance between,
// and null where it is inside none.
bool TryResolveInstanceRelation(int type, VpiHandle ref, VpiHandle& out);

}  // namespace delta
