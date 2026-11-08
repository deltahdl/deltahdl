#pragma once

#include <vector>

namespace delta {

class Arena;
struct EventExpr;
struct ModuleItem;

ModuleItem* WithGlobalClockSubstituted(
    ModuleItem* item, const std::vector<EventExpr>* global_event, Arena& arena);

}  // namespace delta
