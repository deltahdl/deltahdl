#pragma once

#include "common/arena.h"
#include "parser/ast_stmt.h"
#include "simulator/property_clocks.h"

namespace delta {

class SimContext;

// §16.13 with §16.12.17: the clocks the bodies of the named properties the
// tree under `root` instantiates name, their actuals in their formals'
// places, numbered among `clocks` before any attempt has begun. An instance
// is expanded only once an attempt reaches it, and a clock only its body
// names is otherwise met then, after the property's first time steps have
// been read as those of a property on one clock.
void RegisterInstanceBodyClocks(const PropertyExprNode* root,
                                PropertyClocks& clocks, SimContext& ctx,
                                Arena& arena);

}  // namespace delta
