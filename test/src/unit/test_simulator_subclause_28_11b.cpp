// §28.11's Table 28-7 and its illegal-combination sentence, asked of the
// reference model in lib/cpp/test_models/model_strength.h: which level a
// drive-strength keyword carries, and which pair of a strength0 keyword and a
// strength1 keyword the clause rules out.
//
// Every case here calls MapStrengthKeyword or ValidateStrengthPair from
// lib/cpp/test_models/model_strength.h. That is what separates this file from
// test_simulator_subclause_28_11a.cpp beside it: every case there asks the
// production Strength enum in src/common/types.h and the helpers
// IsDrivingStrength and IsChargeStorageStrength declared there, and no case
// there reaches the model.
//
// Issue #3417 is why the model half exists. Both functions were called from
// nowhere, so the levels Table 28-7 gives and the pair §28.11 forbids were
// written down in the model and evaluated by no run.
//
// MapStrengthKeyword takes a position in the keyword encoding
// Parser::ParseStrength0 and Parser::ParseStrength1 produce
// (src/parser/parser_toplevel.cpp): 0 for no strength keyword, 1 for highz0 or
// highz1, 2 for weak0 or weak1, 3 for pull0 or pull1, 4 for strong0 or
// strong1, and 5 for supply0 or supply1. That position is not a strength
// level, and no keyword's position equals its level, so a model that returned
// its argument would fail every case below.
//
// One function answers both halves of a strength specification because
// Table 28-7 gives supply0 and supply1 the level 7, strong0 and strong1 the
// level 6, pull0 and pull1 5, weak0 and weak1 3, and highz0 and highz1 0: the
// suffix says which portion of the net value the strength belongs to and does
// not change the level. §28.11 states the two components as list a), the
// strength of the 0 portion, and list b), the strength of the 1 portion, each
// admitting those same five names.

#include <gtest/gtest.h>

#include <cstdint>

#include "common/types.h"
#include "model_strength.h"

using namespace delta;

namespace {

// The level a model StrengthLevel carries, as the number Table 28-7 gives it.
int LevelOf(StrengthLevel level) { return static_cast<int>(level); }

// The level a production Strength carries, as the same number, so a model
// answer and a production enumerator can be compared.
int LevelOf(Strength strength) { return static_cast<int>(strength); }

// §28.11's Table 28-7 gives highz0 and highz1 the level 0. Keyword index 1 is
// highz.
TEST(StrengthKeywordModel, HighzKeywordCarriesTheHighzLevel) {
  EXPECT_EQ(LevelOf(MapStrengthKeyword(1)), LevelOf(Strength::kHighz));
}

// Table 28-7 gives weak0 and weak1 the level 3. Keyword index 2 is weak.
TEST(StrengthKeywordModel, WeakKeywordCarriesTheWeakLevel) {
  EXPECT_EQ(LevelOf(MapStrengthKeyword(2)), LevelOf(Strength::kWeak));
}

// Table 28-7 gives pull0 and pull1 the level 5. Keyword index 3 is pull.
TEST(StrengthKeywordModel, PullKeywordCarriesThePullLevel) {
  EXPECT_EQ(LevelOf(MapStrengthKeyword(3)), LevelOf(Strength::kPull));
}

// Table 28-7 gives strong0 and strong1 the level 6. Keyword index 4 is strong.
TEST(StrengthKeywordModel, StrongKeywordCarriesTheStrongLevel) {
  EXPECT_EQ(LevelOf(MapStrengthKeyword(4)), LevelOf(Strength::kStrong));
}

// Table 28-7 gives supply0 and supply1 the level 7. Keyword index 5 is supply.
TEST(StrengthKeywordModel, SupplyKeywordCarriesTheSupplyLevel) {
  EXPECT_EQ(LevelOf(MapStrengthKeyword(5)), LevelOf(Strength::kSupply));
}

// Table 28-7 orders the five drive-strength names highz below weak below pull
// below strong below supply, so the five keyword indices give five levels that
// rise with the table's order rather than five equal or five arbitrary ones.
TEST(StrengthKeywordModel, KeywordLevelsRiseInTable287Order) {
  EXPECT_LT(LevelOf(MapStrengthKeyword(1)), LevelOf(MapStrengthKeyword(2)));
  EXPECT_LT(LevelOf(MapStrengthKeyword(2)), LevelOf(MapStrengthKeyword(3)));
  EXPECT_LT(LevelOf(MapStrengthKeyword(3)), LevelOf(MapStrengthKeyword(4)));
  EXPECT_LT(LevelOf(MapStrengthKeyword(4)), LevelOf(MapStrengthKeyword(5)));
}

// Table 28-7 names eight levels, highz at 0 through supply at 7, and every
// answer the model gives is one of them. The loop runs the whole domain of the
// parameter, so it covers index 0 and every index above 5 as well as the five
// keyword indices.
//
// Index 0 says no strength keyword was written, and an index above 5 names no
// keyword at all, so §28.11 decides no level for either. This case therefore
// claims only that the answer stays inside Table 28-7. The model returns
// kHighz for both, which is the model's own choice and is deliberately not
// asserted.
TEST(StrengthKeywordModel, EveryIndexYieldsALevelTable287Names) {
  for (int index = 0; index <= 255; ++index) {
    EXPECT_LE(LevelOf(MapStrengthKeyword(static_cast<uint8_t>(index))),
              LevelOf(Strength::kSupply))
        << "keyword index " << index;
  }
}

// The model's StrengthLevel and the production Strength in src/common/types.h
// carry Table 28-7's eight levels under the same eight names. This is what
// lets the keyword cases above compare a model answer against a production
// enumerator, and it is what goes red if either enum is renumbered.
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

// §28.11: "The combinations (highz0, highz1) and (highz1, highz0) shall be
// considered illegal." Read as levels, both spellings name the one pair whose
// two sides are both highz.
TEST(StrengthPairModel, BothSidesHighzIsIllegal) {
  EXPECT_FALSE(
      ValidateStrengthPair(StrengthLevel::kHighz, StrengthLevel::kHighz));
}

// §28.11 rules out that one pair and no other, so a highz on one side is legal
// whenever the other side carries one of the four driving strengths. Both
// orders are asserted because the clause forbids a pair rather than a side.
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

// Every pair drawn from §28.11's list a) and list b) that names no highz on
// either side is legal, the clause ruling out the highz pair alone.
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
