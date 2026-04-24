#include <gtest/gtest.h>

#include "model_strength.h"

namespace {

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

TEST(StrengthModel, BothHighzIsIllegal) {
  EXPECT_FALSE(
      ValidateStrengthPair(StrengthLevel::kHighz, StrengthLevel::kHighz));
}

TEST(StrengthModel, StrongStrongIsLegal) {
  EXPECT_TRUE(
      ValidateStrengthPair(StrengthLevel::kStrong, StrengthLevel::kStrong));
}

TEST(StrengthModel, OneSideHighzIsLegal) {
  EXPECT_TRUE(
      ValidateStrengthPair(StrengthLevel::kStrong, StrengthLevel::kHighz));
}

}  // namespace
