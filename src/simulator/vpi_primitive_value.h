#pragma once

#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

// The value property §37.35 draws on a primitive and on a prim term, which
// vpi_get_value reads and, for a sequential UDP alone (detail 2),
// vpi_put_value writes.

namespace delta {

class SimContext;

// §37.35: the object whose value `obj` reads: for a prim term the expression
// it connects, and for a primitive the expression its first terminal that it
// drives connects, each null where there is none; `obj` itself for any other
// object.
VpiHandle VpiPrimitiveValueSource(VpiHandle obj);

// §37.35 detail 2 with §38.34: puts `value` to the sequential UDP `obj` stands
// for in the run `sim`, its one bit becoming the running instance's state and
// output at once, a z taken for the x §29.3.5 makes it; a value in a format
// giving no bit writes nothing. Answers whether `obj` is a sequential UDP
// whose instance runs in `sim`, false leaving the put to the caller.
bool VpiPutSequentialUdpValue(const VpiObject& obj, const s_vpi_value* value,
                              SimContext* sim);

}  // namespace delta
