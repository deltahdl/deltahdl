

#include <gtest/gtest.h>

#include "common/types.h"

using namespace delta;

namespace {

TEST(StrengthReductionResistive, SupplyReducesToPull) {
  EXPECT_EQ(ReduceResistive(Strength::kSupply), Strength::kPull);
}

TEST(StrengthReductionResistive, StrongReducesToPull) {
  EXPECT_EQ(ReduceResistive(Strength::kStrong), Strength::kPull);
}

TEST(StrengthReductionResistive, PullReducesToWeak) {
  EXPECT_EQ(ReduceResistive(Strength::kPull), Strength::kWeak);
}

TEST(StrengthReductionResistive, LargeReducesToMedium) {
  EXPECT_EQ(ReduceResistive(Strength::kLarge), Strength::kMedium);
}

TEST(StrengthReductionResistive, WeakReducesToMedium) {
  EXPECT_EQ(ReduceResistive(Strength::kWeak), Strength::kMedium);
}

TEST(StrengthReductionResistive, MediumReducesToSmall) {
  EXPECT_EQ(ReduceResistive(Strength::kMedium), Strength::kSmall);
}

TEST(StrengthReductionResistive, SmallStaysSmall) {
  EXPECT_EQ(ReduceResistive(Strength::kSmall), Strength::kSmall);
}

TEST(StrengthReductionResistive, HighzStaysHighz) {
  EXPECT_EQ(ReduceResistive(Strength::kHighz), Strength::kHighz);
}

}
