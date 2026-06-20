#include <cstdint>

namespace delta {

// §16.12.13: a folded view of the upper bound of the range attached to a ranged
// eventually property. The bound is either the `$` token (an unbounded maximum)
// or a finite clock-tick count carrying its folded value.
struct EventuallyRangeBound {
  bool is_dollar = false;
  std::int64_t value = 0;
};

// §16.12.13: whether the range of a ranged eventually property is permitted for
// the given operator strength. The range for a weak `eventually` shall be
// bounded, so a `$` maximum is rejected there; the range for a strong
// `s_eventually` may be unbounded, so a `$` maximum is accepted.
bool IsEventuallyRangeWellFormed(EventuallyRangeBound upper, bool strong);

// §16.12.13: build a folded finite (bounded) upper bound from a raw value.
EventuallyRangeBound MakeEventuallyBound(std::int64_t value);

// §16.12.13: build the `$` upper bound — an unbounded maximum.
EventuallyRangeBound MakeEventuallyDollar();

}  // namespace delta
