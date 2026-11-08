#include "elaborator/eventually_range.h"

#include <cstdint>

namespace delta {

bool IsEventuallyRangeWellFormed(EventuallyRangeBound upper, bool strong) {
  if (upper.is_dollar) {
    return strong;
  }
  return true;
}

EventuallyRangeBound MakeEventuallyBound(std::int64_t value) {
  return EventuallyRangeBound{false, value};
}

EventuallyRangeBound MakeEventuallyDollar() {
  EventuallyRangeBound bound;
  bound.is_dollar = true;
  return bound;
}

}  // namespace delta
