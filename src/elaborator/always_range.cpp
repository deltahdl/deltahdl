#include "elaborator/always_range.h"

#include <cstdint>

namespace delta {

namespace {

bool IsNonNegativeIntegerConstant(const AlwaysRangeBound& bound) {
  return bound.is_constant && bound.is_integer && bound.value >= 0;
}

}  // namespace

bool IsAlwaysRangeWellFormed(const AlwaysRange& range, bool strong) {
  if (!IsNonNegativeIntegerConstant(range.min)) {
    return false;
  }
  if (range.max.is_dollar) {
    return !strong;
  }
  if (!IsNonNegativeIntegerConstant(range.max)) {
    return false;
  }
  return range.min.value <= range.max.value;
}

AlwaysRangeBound MakeAlwaysBound(std::int64_t value) {
  return AlwaysRangeBound{true, true, false, value};
}

AlwaysRangeBound MakeAlwaysDollar() {
  AlwaysRangeBound bound;
  bound.is_dollar = true;
  return bound;
}

}  // namespace delta
