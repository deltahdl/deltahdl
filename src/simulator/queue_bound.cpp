#include "simulator/queue_bound.h"

#include <cstddef>
#include <format>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"

namespace delta {

bool EnforceQueueBound(QueueObject* q, std::string_view op, SourceLoc loc,
                       SimContext& ctx) {
  if (!q || q->max_size < 0) return false;
  // QueueObject::max_size counts elements, so a queue declared [$:N] carries
  // N + 1 here and an element at index N is the last one it may hold.
  auto limit = static_cast<size_t>(q->max_size);
  if (q->elements.size() <= limit) return false;
  q->elements.resize(limit);
  // The two lists are indexed together, so an element discarded here takes its
  // id with it. A shorter id list is left as it stands, since the caller that
  // left it short assigns the ids itself.
  if (q->element_ids.size() > limit) q->element_ids.resize(limit);
  ctx.GetDiag().Warning(loc, std::format("bounded queue overflow in {}", op),
                        Subclause("7.10.5"));
  return true;
}

}  // namespace delta
