#include <gtest/gtest.h>

#include "common/packed_range.h"

using namespace delta;

namespace {

TEST(PackedRange, ImplicitRangeOfNoBitsIsZeroToZero) {
  PackedRange range = PackedRange::Implicit(0);

  EXPECT_EQ(range.left, 0);
  EXPECT_EQ(range.right, 0);
  EXPECT_EQ(PackedRange::Implicit(8).left, 7);
}

}  // namespace
