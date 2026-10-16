#pragma once

#include <functional>

namespace delta {

struct Expr;
struct VpiObject;

// §37.3.5: hang on `select`, the object standing for the select `expr` the
// source wrote, an index expression object for each of its indexes whose
// evaluation has side effects (VpiSourceExprHasSideEffects), down through the
// selects it is written over -- `a[i++][0]`'s first index among them -- so
// that vpi_put_value() refuses to write through it. `alloc` makes each object.
// Nothing for an expression that is no select or whose indexes have none.
void VpiNoteSelectIndexes(VpiObject* select, const Expr* expr,
                          const std::function<VpiObject*()>& alloc);

}  // namespace delta
