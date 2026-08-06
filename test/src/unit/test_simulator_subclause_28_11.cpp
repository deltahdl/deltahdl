

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

// §28.11: the four driving strengths are supply, strong, pull, and weak.
TEST(StrengthClassification, DrivingStrengthsAreSupplyStrongPullWeak) {
  EXPECT_TRUE(IsDrivingStrength(Strength::kSupply));
  EXPECT_TRUE(IsDrivingStrength(Strength::kStrong));
  EXPECT_TRUE(IsDrivingStrength(Strength::kPull));
  EXPECT_TRUE(IsDrivingStrength(Strength::kWeak));
}

TEST(StrengthClassification, ChargeStorageStrengthsAreNotDriving) {
  EXPECT_FALSE(IsDrivingStrength(Strength::kLarge));
  EXPECT_FALSE(IsDrivingStrength(Strength::kMedium));
  EXPECT_FALSE(IsDrivingStrength(Strength::kSmall));
}

// §28.11: the three charge storage strengths are large, medium, and small.
TEST(StrengthClassification, ChargeStorageStrengthsAreLargeMediumSmall) {
  EXPECT_TRUE(IsChargeStorageStrength(Strength::kLarge));
  EXPECT_TRUE(IsChargeStorageStrength(Strength::kMedium));
  EXPECT_TRUE(IsChargeStorageStrength(Strength::kSmall));
}

TEST(StrengthClassification, DrivingStrengthsAreNotChargeStorage) {
  EXPECT_FALSE(IsChargeStorageStrength(Strength::kSupply));
  EXPECT_FALSE(IsChargeStorageStrength(Strength::kStrong));
  EXPECT_FALSE(IsChargeStorageStrength(Strength::kPull));
  EXPECT_FALSE(IsChargeStorageStrength(Strength::kWeak));
}

// §28.11: highz is neither a driving nor a charge storage strength.
TEST(StrengthClassification, HighzIsNeitherDrivingNorChargeStorage) {
  EXPECT_FALSE(IsDrivingStrength(Strength::kHighz));
  EXPECT_FALSE(IsChargeStorageStrength(Strength::kHighz));
}

}  // namespace
