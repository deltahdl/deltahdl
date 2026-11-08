#include <gtest/gtest.h>

#include "elaborator/sequence_repetition.h"

using namespace delta;

namespace {

TEST(RepetitionCount, ExactCountIsAlwaysWellFormed) {
  EXPECT_TRUE(IsRepetitionCountWellFormed(MakeExactCount(0)));
  EXPECT_TRUE(IsRepetitionCountWellFormed(MakeExactCount(3)));
}

TEST(RepetitionCount, FiniteRangeRequiresMinNoGreaterThanMax) {
  EXPECT_TRUE(IsRepetitionCountWellFormed(MakeFiniteRange(2, 5)));
  EXPECT_TRUE(IsRepetitionCountWellFormed(MakeFiniteRange(3, 3)));
  EXPECT_FALSE(IsRepetitionCountWellFormed(MakeFiniteRange(5, 2)));
}

TEST(RepetitionCount, DollarRangeIsWellFormed) {
  EXPECT_TRUE(IsRepetitionCountWellFormed(MakeDollarRange(0)));
  EXPECT_TRUE(IsRepetitionCountWellFormed(MakeDollarRange(10)));
}

TEST(RepetitionShortcuts, StarAndPlusExpandToDollarRanges) {
  auto star = NormalizeStarShortcut();
  EXPECT_TRUE(star.max_is_dollar);
  EXPECT_EQ(star.min, 0u);

  auto plus = NormalizePlusShortcut();
  EXPECT_TRUE(plus.max_is_dollar);
  EXPECT_EQ(plus.min, 1u);
}

TEST(RepetitionContext, ConsecutiveAllowedOnSequenceAndBoolean) {
  EXPECT_TRUE(IsRepetitionAllowedOn(RepetitionKind::kConsecutive, true, false));
  EXPECT_TRUE(
      IsRepetitionAllowedOn(RepetitionKind::kConsecutive, false, false));
}

TEST(RepetitionContext, GotoAndNonconsecutiveRequireBareBoolean) {
  EXPECT_FALSE(IsRepetitionAllowedOn(RepetitionKind::kGoto, false, false));
  EXPECT_TRUE(IsRepetitionAllowedOn(RepetitionKind::kGoto, true, false));
  EXPECT_FALSE(IsRepetitionAllowedOn(RepetitionKind::kGoto, true, true));
  EXPECT_FALSE(
      IsRepetitionAllowedOn(RepetitionKind::kNonconsecutive, true, true));
}

TEST(RepetitionContext, NonconsecutiveRequiresBareBoolean) {
  EXPECT_FALSE(
      IsRepetitionAllowedOn(RepetitionKind::kNonconsecutive, false, false));
  EXPECT_TRUE(
      IsRepetitionAllowedOn(RepetitionKind::kNonconsecutive, true, false));
}

TEST(RepetitionZero, OnlyConsecutivePermitsZeroIterations) {
  EXPECT_TRUE(IsZeroRepetitionPermitted(RepetitionKind::kConsecutive));
  EXPECT_FALSE(IsZeroRepetitionPermitted(RepetitionKind::kGoto));
  EXPECT_FALSE(IsZeroRepetitionPermitted(RepetitionKind::kNonconsecutive));
}

}  // namespace
