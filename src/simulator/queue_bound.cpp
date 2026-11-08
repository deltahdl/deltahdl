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
  auto limit = static_cast<size_t>(q->max_size);
  if (q->elements.size() <= limit) return false;
  q->elements.resize(limit);
  if (q->element_ids.size() > limit) q->element_ids.resize(limit);
  ctx.GetDiag().Warning(loc, std::format("bounded queue overflow in {}", op),
                        Subclause("7.10.5"));
  return true;
}

}  // namespace delta
