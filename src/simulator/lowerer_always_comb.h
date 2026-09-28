#pragma once

#include <string_view>
#include <vector>

#include "parser/ast_stmt.h"

namespace delta {

class SimContext;

// §9.2.2.2.1: the names an always_comb or always_latch procedure re-runs on
// a change of. The inferred sensitivity list `sens`, which descends into the
// functions the block calls and reduces each read to its base name, already
// leaves out the block's locals and what it writes. This further drops a
// variable passed to a called subroutine's output formal, which the call
// writes rather than reads; a class handle, since references to class objects
// add nothing to the list; and a name nothing can watch
// (DropUnwatchableNames).
std::vector<std::string_view> AlwaysCombWatchedNames(
    const Stmt* body, const std::vector<EventExpr>& sens, SimContext& ctx);

}  // namespace delta
