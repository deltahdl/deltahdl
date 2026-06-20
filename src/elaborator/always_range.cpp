#include "elaborator/always_range.h"

namespace delta {

namespace {

// §16.12.11: a bound is a usable non-negative integer constant when it folded
// to a constant, is integer-valued, and is not negative.
bool IsNonNegativeIntegerConstant(const AlwaysRangeBound& bound) {
  return bound.is_constant && bound.is_integer && bound.value >= 0;
}

}  // namespace

// §16.12.11: enforce the range restrictions. The minimum is always a
// non-negative integer constant expression. The maximum is either `$` or a
// non-negative integer constant expression; `$` is permitted only for the weak
// form because a strong always range shall be bounded. When both bounds are
// integer constants the minimum shall be less than or equal to the maximum.
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

// §16.12.11: a folded constant-integer bound built from a raw value.
AlwaysRangeBound MakeAlwaysBound(std::int64_t value) {
  return AlwaysRangeBound{/*is_constant=*/true, /*is_integer=*/true,
                          /*is_dollar=*/false, value};
}

// §16.12.11: the `$` maximum — finite but unbounded.
AlwaysRangeBound MakeAlwaysDollar() {
  AlwaysRangeBound bound;
  bound.is_dollar = true;
  return bound;
}

}  // namespace delta
