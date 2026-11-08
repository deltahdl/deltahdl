#include <cstdint>

namespace delta {

struct EventuallyRangeBound {
  bool is_dollar = false;
  std::int64_t value = 0;
};

bool IsEventuallyRangeWellFormed(EventuallyRangeBound upper, bool strong);

EventuallyRangeBound MakeEventuallyBound(std::int64_t value);

EventuallyRangeBound MakeEventuallyDollar();

}  // namespace delta
