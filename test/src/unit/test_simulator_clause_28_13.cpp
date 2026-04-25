// §28.13

#include <gtest/gtest.h>

#include "common/types.h"

using namespace delta;

namespace {

// §28.13's only transformation: a supply strength flowing through any of the
// nonresistive switches (nmos/pmos/cmos and tran/tranif*) emerges reduced to
// strong. The production reducer is the single place that encodes that rule;
// verify the reduction happens.
TEST(StrengthReductionNonresistive, SupplyReducesToStrong) {
  EXPECT_EQ(ReduceNonresistive(Strength::kSupply), Strength::kStrong);
}

// §28.13 names supply as the sole exception. The remaining seven driving and
// charge-storage levels of Table 28-7 must traverse a nonresistive switch
// unchanged. Each level below pins one row of that table against the reducer.
TEST(StrengthReductionNonresistive, StrongPassesThrough) {
  EXPECT_EQ(ReduceNonresistive(Strength::kStrong), Strength::kStrong);
}

TEST(StrengthReductionNonresistive, PullPassesThrough) {
  EXPECT_EQ(ReduceNonresistive(Strength::kPull), Strength::kPull);
}

TEST(StrengthReductionNonresistive, LargePassesThrough) {
  EXPECT_EQ(ReduceNonresistive(Strength::kLarge), Strength::kLarge);
}

TEST(StrengthReductionNonresistive, WeakPassesThrough) {
  EXPECT_EQ(ReduceNonresistive(Strength::kWeak), Strength::kWeak);
}

TEST(StrengthReductionNonresistive, MediumPassesThrough) {
  EXPECT_EQ(ReduceNonresistive(Strength::kMedium), Strength::kMedium);
}

TEST(StrengthReductionNonresistive, SmallPassesThrough) {
  EXPECT_EQ(ReduceNonresistive(Strength::kSmall), Strength::kSmall);
}

TEST(StrengthReductionNonresistive, HighzPassesThrough) {
  EXPECT_EQ(ReduceNonresistive(Strength::kHighz), Strength::kHighz);
}

}  // namespace
