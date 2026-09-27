#include <gtest/gtest.h>

#include "common/packed_range.h"

using namespace delta;

namespace {

// No clause of IEEE 1800-2023 gives a vector of no bits a range, so this case
// covers PackedRange::Implicit on its own terms. A name that resolves to no
// signal reports a width of zero, and the range it is addressed with has to
// keep its left bound at or above its right one: [-1:0] would read as an
// ascending range and invert the mapping from index to offset.
TEST(PackedRange, ImplicitRangeOfNoBitsIsZeroToZero) {
  PackedRange range = PackedRange::Implicit(0);

  EXPECT_EQ(range.left, 0);
  EXPECT_EQ(range.right, 0);
  EXPECT_EQ(PackedRange::Implicit(8).left, 7);
}

}  // namespace
