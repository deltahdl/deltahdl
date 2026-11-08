#pragma once

#include <string_view>

#include "common/source_loc.h"

namespace delta {

struct QueueObject;
class SimContext;

bool EnforceQueueBound(QueueObject* q, std::string_view op, SourceLoc loc,
                       SimContext& ctx);

}  // namespace delta
