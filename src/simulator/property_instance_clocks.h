#pragma once

#include "common/arena.h"
#include "parser/ast_stmt.h"
#include "simulator/property_clocks.h"

namespace delta {

class SimContext;

void RegisterInstanceBodyClocks(const PropertyExprNode* root,
                                PropertyClocks& clocks, SimContext& ctx,
                                Arena& arena);

}  // namespace delta
