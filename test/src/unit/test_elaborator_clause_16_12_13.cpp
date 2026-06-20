#include <gtest/gtest.h>

#include "elaborator/eventually_range.h"

using namespace delta;

namespace {

// §16.12.13: a weak `eventually` with a bounded range is well-formed.
TEST(EventuallyRange, WeakEventuallyAllowsBoundedRange) {
  EXPECT_TRUE(
      IsEventuallyRangeWellFormed(MakeEventuallyBound(5), /*strong=*/false));
}

// §16.12.13: the range for a weak eventually shall be bounded, so a `$` upper
// bound is rejected for `eventually` (the `eventually [2:$]` form is illegal).
TEST(EventuallyRange, WeakEventuallyRejectsUnboundedMaximum) {
  EXPECT_FALSE(
      IsEventuallyRangeWellFormed(MakeEventuallyDollar(), /*strong=*/false));
}

// §16.12.13: the range for a strong eventually may be unbounded, so a `$` upper
// bound is accepted for `s_eventually` even though the same bound is illegal
// for the weak form.
TEST(EventuallyRange, StrongEventuallyAllowsUnboundedMaximum) {
  EXPECT_TRUE(
      IsEventuallyRangeWellFormed(MakeEventuallyDollar(), /*strong=*/true));
}

// §16.12.13: a strong eventually with a bounded range remains well-formed.
TEST(EventuallyRange, StrongEventuallyAllowsBoundedRange) {
  EXPECT_TRUE(
      IsEventuallyRangeWellFormed(MakeEventuallyBound(2), /*strong=*/true));
}

}  // namespace
