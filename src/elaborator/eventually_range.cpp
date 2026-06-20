#include "elaborator/eventually_range.h"

namespace delta {

// §16.12.13: only an unbounded (`$`) upper bound is constrained by this
// subclause. A weak `eventually` range shall be bounded, so an unbounded
// maximum is rejected for it; a strong `s_eventually` range may be unbounded,
// so the same maximum is accepted there. Any finite upper bound is permitted
// for both forms.
bool IsEventuallyRangeWellFormed(EventuallyRangeBound upper, bool strong) {
  if (upper.is_dollar) {
    return strong;
  }
  return true;
}

// §16.12.13: a finite upper bound carrying its folded clock-tick count.
EventuallyRangeBound MakeEventuallyBound(std::int64_t value) {
  return EventuallyRangeBound{/*is_dollar=*/false, value};
}

// §16.12.13: the `$` upper bound — an unbounded maximum.
EventuallyRangeBound MakeEventuallyDollar() {
  EventuallyRangeBound bound;
  bound.is_dollar = true;
  return bound;
}

}  // namespace delta
