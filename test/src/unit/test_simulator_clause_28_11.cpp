// §28.11: Logic strength modeling

#include <gtest/gtest.h>

#include "model_strength.h"

namespace {

// =============================================================
// §28.11: Logic strength modeling
// =============================================================
// §28.11: Table 28-7 — strength level mapping.
TEST(StrengthModel, SupplyIsLevel7) {
  EXPECT_EQ(static_cast<uint8_t>(StrengthLevel::kSupply), 7);
}

TEST(StrengthModel, StrongIsLevel6) {
  EXPECT_EQ(static_cast<uint8_t>(StrengthLevel::kStrong), 6);
}

TEST(StrengthModel, PullIsLevel5) {
  EXPECT_EQ(static_cast<uint8_t>(StrengthLevel::kPull), 5);
}

TEST(StrengthModel, LargeIsLevel4) {
  EXPECT_EQ(static_cast<uint8_t>(StrengthLevel::kLarge), 4);
}

TEST(StrengthModel, WeakIsLevel3) {
  EXPECT_EQ(static_cast<uint8_t>(StrengthLevel::kWeak), 3);
}

TEST(StrengthModel, MediumIsLevel2) {
  EXPECT_EQ(static_cast<uint8_t>(StrengthLevel::kMedium), 2);
}

TEST(StrengthModel, SmallIsLevel1) {
  EXPECT_EQ(static_cast<uint8_t>(StrengthLevel::kSmall), 1);
}

TEST(StrengthModel, HighzIsLevel0) {
  EXPECT_EQ(static_cast<uint8_t>(StrengthLevel::kHighz), 0);
}

// §28.11: "(highz0, highz1) and (highz1, highz0) shall be
//  considered illegal."
TEST(StrengthModel, BothHighzIsIllegal) {
  EXPECT_FALSE(
      ValidateStrengthPair(StrengthLevel::kHighz, StrengthLevel::kHighz));
}

// §28.11: Other combinations are legal.
TEST(StrengthModel, StrongStrongIsLegal) {
  EXPECT_TRUE(
      ValidateStrengthPair(StrengthLevel::kStrong, StrengthLevel::kStrong));
}

TEST(StrengthModel, StrongHighz1IsLegal) {
  EXPECT_TRUE(
      ValidateStrengthPair(StrengthLevel::kStrong, StrengthLevel::kHighz));
}

TEST(StrengthModel, Highz0StrongIsLegal) {
  EXPECT_TRUE(
      ValidateStrengthPair(StrengthLevel::kHighz, StrengthLevel::kStrong));
}

}  // namespace
