#pragma once

#include <vector>

namespace delta {

class Arena;
struct EventExpr;
struct ModuleItem;

// The declaration of a subroutine as one instance of its module sees it, with
// every `$global_clock` its body names replaced by `global_event`; `item`
// itself where nothing is replaced.
ModuleItem* WithGlobalClockSubstituted(
    ModuleItem* item, const std::vector<EventExpr>* global_event, Arena& arena);

}  // namespace delta
