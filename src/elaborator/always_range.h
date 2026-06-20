#include <cstdint>

namespace delta {

// §16.12.11: a folded view of one bound of the range attached to a ranged
// `always`/`s_always` property. A bound carries the facts the range
// restrictions in this subclause depend on: whether the operand folded to a
// compile-time constant, whether it is integer-valued, whether it is the `$`
// token (a finite but unbounded maximum), and the folded value itself.
struct AlwaysRangeBound {
  bool is_constant = false;
  bool is_integer = false;
  bool is_dollar = false;
  std::int64_t value = 0;
};

// §16.12.11: the folded minimum and maximum bounds of a ranged always.
struct AlwaysRange {
  AlwaysRangeBound min;
  AlwaysRangeBound max;
};

// §16.12.11: whether a ranged always range satisfies this subclause's
// restrictions for the given operator strength. The minimum shall be a
// non-negative integer constant expression; the maximum shall be a non-negative
// integer constant expression or `$`; when both bounds are integer constant
// expressions the minimum shall not exceed the maximum. The range for a strong
// always (`s_always`) shall be bounded, so a `$` maximum is rejected there
// while it is allowed for a weak always.
bool IsAlwaysRangeWellFormed(const AlwaysRange& range, bool strong);

// §16.12.11: build a folded constant-integer bound from a raw value (the common
// case in tests and in folded ASTs).
AlwaysRangeBound MakeAlwaysBound(std::int64_t value);

// §16.12.11: build the `$` maximum bound — a finite but unbounded maximum.
AlwaysRangeBound MakeAlwaysDollar();

}  // namespace delta
