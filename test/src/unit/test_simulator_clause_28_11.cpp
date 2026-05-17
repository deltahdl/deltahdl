

#include <gtest/gtest.h>

#include "common/types.h"

using namespace delta;

namespace {

TEST(StrengthLevel, SupplyIsLevel7) {
  EXPECT_EQ(static_cast<uint8_t>(Strength::kSupply), 7);
}

TEST(StrengthLevel, StrongIsLevel6) {
  EXPECT_EQ(static_cast<uint8_t>(Strength::kStrong), 6);
}

TEST(StrengthLevel, PullIsLevel5) {
  EXPECT_EQ(static_cast<uint8_t>(Strength::kPull), 5);
}

TEST(StrengthLevel, LargeIsLevel4) {
  EXPECT_EQ(static_cast<uint8_t>(Strength::kLarge), 4);
}

TEST(StrengthLevel, WeakIsLevel3) {
  EXPECT_EQ(static_cast<uint8_t>(Strength::kWeak), 3);
}

TEST(StrengthLevel, MediumIsLevel2) {
  EXPECT_EQ(static_cast<uint8_t>(Strength::kMedium), 2);
}

TEST(StrengthLevel, SmallIsLevel1) {
  EXPECT_EQ(static_cast<uint8_t>(Strength::kSmall), 1);
}

TEST(StrengthLevel, HighzIsLevel0) {
  EXPECT_EQ(static_cast<uint8_t>(Strength::kHighz), 0);
}

TEST(StrengthLevel, StrengthValPacksBothSidesIndependently) {
  StrengthVal sv{};
  sv.s0 = static_cast<uint8_t>(Strength::kPull);
  sv.s1 = static_cast<uint8_t>(Strength::kSupply);
  EXPECT_EQ(sv.s0, 5);
  EXPECT_EQ(sv.s1, 7);
}

}
