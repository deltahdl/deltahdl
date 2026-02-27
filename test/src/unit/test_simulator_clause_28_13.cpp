// §28.13: Strength reduction by nonresistive devices

#include <gtest/gtest.h>

#include "model_strength.h"

namespace {

// =============================================================
// §28.13: Strength reduction by nonresistive devices
// =============================================================
// §28.13: "nmos, pmos, and cmos switches shall pass the strength
//  from the data input to the output, except that a supply strength
//  shall be reduced to a strong strength."
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
