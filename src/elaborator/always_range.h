#include <cstdint>

namespace delta {

struct AlwaysRangeBound {
  bool is_constant = false;
  bool is_integer = false;
  bool is_dollar = false;
  std::int64_t value = 0;
};

struct AlwaysRange {
  AlwaysRangeBound min;
  AlwaysRangeBound max;
};

bool IsAlwaysRangeWellFormed(const AlwaysRange& range, bool strong);

AlwaysRangeBound MakeAlwaysBound(std::int64_t value);

AlwaysRangeBound MakeAlwaysDollar();

}  // namespace delta
