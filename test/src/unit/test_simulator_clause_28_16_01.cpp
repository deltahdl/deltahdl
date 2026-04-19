#include <gtest/gtest.h>

#include "helpers_mintymax.h"

namespace {

// §28.16.1 R1: runtime delay selection must return the min branch in slot 0.
TEST(MinTypMaxDelays, SelectMin) {
  MinTypMax mtm{5, 10, 15};
  EXPECT_EQ(SelectMinTypMax(mtm, 0), 5u);
}

// §28.16.1 R1: runtime delay selection must return the typ branch in slot 1.
TEST(MinTypMaxDelays, SelectTyp) {
  MinTypMax mtm{5, 10, 15};
  EXPECT_EQ(SelectMinTypMax(mtm, 1), 10u);
}

// §28.16.1 R1: runtime delay selection must return the max branch in slot 2.
TEST(MinTypMaxDelays, SelectMax) {
  MinTypMax mtm{5, 10, 15};
  EXPECT_EQ(SelectMinTypMax(mtm, 2), 15u);
}

// §28.16.1 R2: min/typ/max have no required ordering — a spec where the
// literal min value exceeds typ must still select each field as stored, so
// the runtime helper cannot silently re-sort.
TEST(MinTypMaxDelays, NoRequiredOrdering) {
  MinTypMax mtm{20, 5, 10};
  EXPECT_EQ(SelectMinTypMax(mtm, 0), 20u);
  EXPECT_EQ(SelectMinTypMax(mtm, 1), 5u);
  EXPECT_EQ(SelectMinTypMax(mtm, 2), 10u);
}

}  // namespace
