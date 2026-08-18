#pragma once

#include <string_view>

#include "common/source_loc.h"

namespace delta {

struct QueueObject;
class SimContext;

// §7.10.5 — discards every element of `q` that sits beyond the upper bound its
// declaration gave it, and warns that it did. That is what the subclause
// requires after any operation that writes to a bounded queue, so an operation
// that can leave the queue longer than its bound calls this once it has
// finished writing. `op` names that operation in the warning, which reads
// "bounded queue overflow in push_back" for `op` of "push_back". An unbounded
// queue and one that is within its bound are left alone, and the return value
// says whether anything was discarded.
//
// A caller may write past the bound and call this afterwards rather than
// testing the bound first. The subclause's own note allows an implementation
// not to write the out-of-bounds elements at all, so the two orders leave the
// same queue and issue the same warning.
bool EnforceQueueBound(QueueObject* q, std::string_view op, SourceLoc loc,
                       SimContext& ctx);

}  // namespace delta
