#include <gtest/gtest.h>

#include "model_strength.h"

namespace {

TEST(StrengthReduction, ResistiveSupplyToPull) {
  EXPECT_EQ(ReduceResistive(StrengthLevel::kSupply), StrengthLevel::kPull);
}

TEST(StrengthReduction, ResistiveStrongToPull) {
  EXPECT_EQ(ReduceResistive(StrengthLevel::kStrong), StrengthLevel::kPull);
}

TEST(StrengthReduction, ResistivePullToWeak) {
  EXPECT_EQ(ReduceResistive(StrengthLevel::kPull), StrengthLevel::kWeak);
}

TEST(StrengthReduction, ResistiveLargeToMedium) {
  EXPECT_EQ(ReduceResistive(StrengthLevel::kLarge), StrengthLevel::kMedium);
}

TEST(StrengthReduction, ResistiveWeakToMedium) {
  EXPECT_EQ(ReduceResistive(StrengthLevel::kWeak), StrengthLevel::kMedium);
}

TEST(StrengthReduction, ResistiveMediumToSmall) {
  EXPECT_EQ(ReduceResistive(StrengthLevel::kMedium), StrengthLevel::kSmall);
}

TEST(StrengthReduction, ResistiveSmallToSmall) {
  EXPECT_EQ(ReduceResistive(StrengthLevel::kSmall), StrengthLevel::kSmall);
}

TEST(StrengthReduction, ResistiveHighzToHighz) {
  EXPECT_EQ(ReduceResistive(StrengthLevel::kHighz), StrengthLevel::kHighz);
}

}
