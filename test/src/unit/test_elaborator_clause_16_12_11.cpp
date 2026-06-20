#include <gtest/gtest.h>

#include "elaborator/always_range.h"

using namespace delta;

namespace {

// §16.12.11: the minimum is a non-negative integer constant expression and the
// maximum is a non-negative integer constant expression, so a bounded
// non-negative range is well-formed for a weak always.
TEST(AlwaysRange, BoundedNonNegativeRangeIsWellFormed) {
  AlwaysRange range{MakeAlwaysBound(0), MakeAlwaysBound(3)};
  EXPECT_TRUE(IsAlwaysRangeWellFormed(range, /*strong=*/false));
}

// §16.12.11: equal bounds satisfy the "less than or equal to" relation between
// the minimum and the maximum.
TEST(AlwaysRange, EqualBoundsAreWellFormed) {
  AlwaysRange range{MakeAlwaysBound(2), MakeAlwaysBound(2)};
  EXPECT_TRUE(IsAlwaysRangeWellFormed(range, /*strong=*/false));
}

// §16.12.11: a weak always range may be unbounded, so a `$` maximum is
// accepted.
TEST(AlwaysRange, WeakAlwaysAllowsUnboundedMaximum) {
  AlwaysRange range{MakeAlwaysBound(1), MakeAlwaysDollar()};
  EXPECT_TRUE(IsAlwaysRangeWellFormed(range, /*strong=*/false));
}

// §16.12.11: the range for a strong always shall be bounded, so a `$` maximum
// is rejected for `s_always` even though the same range is legal for a weak
// always.
TEST(AlwaysRange, StrongAlwaysRejectsUnboundedMaximum) {
  AlwaysRange range{MakeAlwaysBound(1), MakeAlwaysDollar()};
  EXPECT_FALSE(IsAlwaysRangeWellFormed(range, /*strong=*/true));
}

// §16.12.11: a bounded range remains well-formed for a strong always.
TEST(AlwaysRange, StrongAlwaysAcceptsBoundedRange) {
  AlwaysRange range{MakeAlwaysBound(0), MakeAlwaysBound(4)};
  EXPECT_TRUE(IsAlwaysRangeWellFormed(range, /*strong=*/true));
}

// §16.12.11: when both bounds are integer constants the minimum shall not
// exceed the maximum, so an inverted range is rejected.
TEST(AlwaysRange, MinimumGreaterThanMaximumIsRejected) {
  AlwaysRange range{MakeAlwaysBound(5), MakeAlwaysBound(2)};
  EXPECT_FALSE(IsAlwaysRangeWellFormed(range, /*strong=*/false));
}

// §16.12.11: the minimum shall be a non-negative integer constant expression,
// so a negative minimum is rejected.
TEST(AlwaysRange, NegativeMinimumIsRejected) {
  AlwaysRange range{MakeAlwaysBound(-1), MakeAlwaysBound(3)};
  EXPECT_FALSE(IsAlwaysRangeWellFormed(range, /*strong=*/false));
}

// §16.12.11: the maximum shall be a non-negative integer constant expression
// (or
// `$`), so a negative maximum is rejected.
TEST(AlwaysRange, NegativeMaximumIsRejected) {
  AlwaysRange range{MakeAlwaysBound(0), MakeAlwaysBound(-2)};
  EXPECT_FALSE(IsAlwaysRangeWellFormed(range, /*strong=*/false));
}

// §16.12.11: a bound that does not fold to a compile-time constant is not a
// constant expression and is rejected even though its recorded value is a
// non-negative integer.
TEST(AlwaysRange, NonConstantBoundIsRejected) {
  AlwaysRangeBound non_constant;
  non_constant.is_constant = false;
  non_constant.is_integer = true;
  non_constant.value = 2;
  AlwaysRange range{non_constant, MakeAlwaysBound(4)};
  EXPECT_FALSE(IsAlwaysRangeWellFormed(range, /*strong=*/false));
}

// §16.12.11: a bound shall be integer-valued, so a non-integer constant is
// rejected.
TEST(AlwaysRange, NonIntegerBoundIsRejected) {
  AlwaysRangeBound non_integer;
  non_integer.is_constant = true;
  non_integer.is_integer = false;
  non_integer.value = 1;
  AlwaysRange range{MakeAlwaysBound(0), non_integer};
  EXPECT_FALSE(IsAlwaysRangeWellFormed(range, /*strong=*/false));
}

}  // namespace
