#pragma once

#include <string_view>
#include <vector>

#include "parser/ast_stmt.h"

namespace delta {

class Arena;
class SimContext;

// §9.2.2.2.1 and §9.4.2.2: the names of the elements of the fixed-size
// unpacked array `name`, down through every unpacked dimension, or none where
// `name` is no such array. A read through a non-constant index, `a[j]`, reads
// the whole array, and each element is a Variable of its own that a write
// notifies under its own name and never under the array's, so a process that
// reads the array is woken through these.
std::vector<std::string_view> UnpackedElementNames(std::string_view name,
                                                   SimContext& ctx);

// §9.4.2.2: the implicit event_expression list `sens` of an `always @*`, with
// an event added on each element of every fixed-size unpacked array it names
// (UnpackedElementNames). The list is held by `arena` for the life of the
// process.
const std::vector<EventExpr>& ImplicitListEvents(
    const std::vector<EventExpr>& sens, SimContext& ctx, Arena& arena);

// §9.2.2.2.1: the names an always_comb or always_latch procedure re-runs on
// a change of. The inferred sensitivity list `sens`, which descends into the
// functions the block calls and reduces each read to its base name, already
// leaves out the block's locals and what it writes. This further drops a
// variable passed to a called subroutine's output formal, which the call
// writes rather than reads; a class handle, since references to class objects
// add nothing to the list; and a name nothing can watch
// (DropUnwatchableNames). A fixed-size unpacked array is watched through each
// of its elements as well (UnpackedElementNames).
std::vector<std::string_view> AlwaysCombWatchedNames(
    const Stmt* body, const std::vector<EventExpr>& sens, SimContext& ctx);

}  // namespace delta
