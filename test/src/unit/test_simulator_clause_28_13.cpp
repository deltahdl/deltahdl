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

}  // namespace
