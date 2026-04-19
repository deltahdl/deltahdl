#include <gtest/gtest.h>

#include "model_strength.h"

namespace {

TEST(StrengthReduction, NonresistivePassesStrong) {
  EXPECT_EQ(ReduceNonresistive(StrengthLevel::kStrong), StrengthLevel::kStrong);
}

TEST(StrengthReduction, NonresistivePassesPull) {
  EXPECT_EQ(ReduceNonresistive(StrengthLevel::kPull), StrengthLevel::kPull);
}

TEST(StrengthReduction, NonresistivePassesWeak) {
  EXPECT_EQ(ReduceNonresistive(StrengthLevel::kWeak), StrengthLevel::kWeak);
}

TEST(StrengthReduction, NonresistiveReducesSupplyToStrong) {
  EXPECT_EQ(ReduceNonresistive(StrengthLevel::kSupply), StrengthLevel::kStrong);
}

TEST(StrengthReduction, NonresistivePassesHighz) {
  EXPECT_EQ(ReduceNonresistive(StrengthLevel::kHighz), StrengthLevel::kHighz);
}

// §28.13 names supply as the sole exception; every other strength — including
// the three charge-storage levels — must pass through unchanged. The three
// tests below close the coverage for the "all others unchanged" clause.
TEST(StrengthReduction, NonresistivePassesLarge) {
  EXPECT_EQ(ReduceNonresistive(StrengthLevel::kLarge), StrengthLevel::kLarge);
}

TEST(StrengthReduction, NonresistivePassesMedium) {
  EXPECT_EQ(ReduceNonresistive(StrengthLevel::kMedium), StrengthLevel::kMedium);
}

TEST(StrengthReduction, NonresistivePassesSmall) {
  EXPECT_EQ(ReduceNonresistive(StrengthLevel::kSmall), StrengthLevel::kSmall);
}

}  // namespace
