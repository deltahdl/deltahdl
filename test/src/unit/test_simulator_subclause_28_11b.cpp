#include <gtest/gtest.h>

#include <cstdint>

#include "common/types.h"
#include "model_strength.h"

using namespace delta;

namespace {

int LevelOf(StrengthLevel level) { return static_cast<int>(level); }

int LevelOf(Strength strength) { return static_cast<int>(strength); }

TEST(StrengthKeywordModel, HighzKeywordCarriesTheHighzLevel) {
  EXPECT_EQ(LevelOf(MapStrengthKeyword(1)), LevelOf(Strength::kHighz));
}

TEST(StrengthKeywordModel, WeakKeywordCarriesTheWeakLevel) {
  EXPECT_EQ(LevelOf(MapStrengthKeyword(2)), LevelOf(Strength::kWeak));
}

TEST(StrengthKeywordModel, PullKeywordCarriesThePullLevel) {
  EXPECT_EQ(LevelOf(MapStrengthKeyword(3)), LevelOf(Strength::kPull));
}

TEST(StrengthKeywordModel, StrongKeywordCarriesTheStrongLevel) {
  EXPECT_EQ(LevelOf(MapStrengthKeyword(4)), LevelOf(Strength::kStrong));
}

TEST(StrengthKeywordModel, SupplyKeywordCarriesTheSupplyLevel) {
  EXPECT_EQ(LevelOf(MapStrengthKeyword(5)), LevelOf(Strength::kSupply));
}

TEST(StrengthKeywordModel, KeywordLevelsRiseFromHighzToSupply) {
  EXPECT_LT(LevelOf(MapStrengthKeyword(1)), LevelOf(MapStrengthKeyword(2)));
  EXPECT_LT(LevelOf(MapStrengthKeyword(2)), LevelOf(MapStrengthKeyword(3)));
  EXPECT_LT(LevelOf(MapStrengthKeyword(3)), LevelOf(MapStrengthKeyword(4)));
  EXPECT_LT(LevelOf(MapStrengthKeyword(4)), LevelOf(MapStrengthKeyword(5)));
}

TEST(StrengthKeywordModel, EveryIndexYieldsANamedStrengthLevel) {
  for (int index = 0; index <= 255; ++index) {
    EXPECT_LE(LevelOf(MapStrengthKeyword(static_cast<uint8_t>(index))),
              LevelOf(Strength::kSupply))
        << "keyword index " << index;
  }
}

TEST(ModelAndProductionStrength, EveryEnumeratorCarriesTheSameLevel) {
  EXPECT_EQ(LevelOf(StrengthLevel::kHighz), LevelOf(Strength::kHighz));
  EXPECT_EQ(LevelOf(StrengthLevel::kSmall), LevelOf(Strength::kSmall));
  EXPECT_EQ(LevelOf(StrengthLevel::kMedium), LevelOf(Strength::kMedium));
  EXPECT_EQ(LevelOf(StrengthLevel::kWeak), LevelOf(Strength::kWeak));
  EXPECT_EQ(LevelOf(StrengthLevel::kLarge), LevelOf(Strength::kLarge));
  EXPECT_EQ(LevelOf(StrengthLevel::kPull), LevelOf(Strength::kPull));
  EXPECT_EQ(LevelOf(StrengthLevel::kStrong), LevelOf(Strength::kStrong));
  EXPECT_EQ(LevelOf(StrengthLevel::kSupply), LevelOf(Strength::kSupply));
}

TEST(StrengthPairModel, BothSidesHighzIsIllegal) {
  EXPECT_FALSE(
      ValidateStrengthPair(StrengthLevel::kHighz, StrengthLevel::kHighz));
}

TEST(StrengthPairModel, HighzOppositeADrivingStrengthIsLegal) {
  const StrengthLevel kDrivingLevels[] = {
      StrengthLevel::kSupply,
      StrengthLevel::kStrong,
      StrengthLevel::kPull,
      StrengthLevel::kWeak,
  };
  for (auto level : kDrivingLevels) {
    EXPECT_TRUE(ValidateStrengthPair(StrengthLevel::kHighz, level))
        << "strength1 level " << LevelOf(level);
    EXPECT_TRUE(ValidateStrengthPair(level, StrengthLevel::kHighz))
        << "strength0 level " << LevelOf(level);
  }
}

TEST(StrengthPairModel, TwoDrivingStrengthsAreLegal) {
  const StrengthLevel kDrivingLevels[] = {
      StrengthLevel::kSupply,
      StrengthLevel::kStrong,
      StrengthLevel::kPull,
      StrengthLevel::kWeak,
  };
  for (auto s0 : kDrivingLevels) {
    for (auto s1 : kDrivingLevels) {
      EXPECT_TRUE(ValidateStrengthPair(s0, s1))
          << "strength0 level " << LevelOf(s0) << ", strength1 level "
          << LevelOf(s1);
    }
  }
}

}  // namespace
