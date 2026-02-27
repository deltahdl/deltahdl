// §28.12.1: Combined signals of unambiguous strength

#include <gtest/gtest.h>

#include "model_strength.h"

namespace {

// =============================================================
// §28.12.1: Combined signals of unambiguous strength
// =============================================================
// §28.12.1: "If two or more signals of unequal strength combine ...
//  the stronger signal shall dominate."
TEST(StrengthCombine, StrongerSignalDominates) {
  StrengthSignal strong_one{Val4::kV1, StrengthLevel::kHighz,
                            StrengthLevel::kStrong};
  StrengthSignal weak_zero{Val4::kV0, StrengthLevel::kWeak,
                           StrengthLevel::kHighz};
  auto result = CombineUnambiguous(strong_one, weak_zero);
  EXPECT_EQ(result.value, Val4::kV1);
}

// §28.12.1: "The combination of two or more signals of like value
//  shall result in the same value with the greater of all the
//  strengths."
TEST(StrengthCombine, LikeValueTakesGreaterStrength) {
  StrengthSignal pull_one{Val4::kV1, StrengthLevel::kHighz,
                          StrengthLevel::kPull};
  StrengthSignal strong_one{Val4::kV1, StrengthLevel::kHighz,
                            StrengthLevel::kStrong};
  auto result = CombineUnambiguous(pull_one, strong_one);
  EXPECT_EQ(result.value, Val4::kV1);
  EXPECT_EQ(result.strength1_hi, StrengthLevel::kStrong);
}

// §28.12.1: "The combination of signals identical in strength and
//  value shall result in the same signal."
TEST(StrengthCombine, IdenticalSignalsUnchanged) {
  StrengthSignal sig{Val4::kV0, StrengthLevel::kPull, StrengthLevel::kHighz};
  auto result = CombineUnambiguous(sig, sig);
  EXPECT_EQ(result.value, Val4::kV0);
  EXPECT_EQ(result.strength0_hi, StrengthLevel::kPull);
}

// §28.12.1: Equal strength, unlike values (no wired logic) → x.
TEST(StrengthCombine, EqualStrengthOppositeValueProducesX) {
  StrengthSignal pull_one{Val4::kV1, StrengthLevel::kHighz,
                          StrengthLevel::kPull};
  StrengthSignal pull_zero{Val4::kV0, StrengthLevel::kPull,
                           StrengthLevel::kHighz};
  auto result = CombineUnambiguous(pull_one, pull_zero);
  EXPECT_EQ(result.value, Val4::kX);
}

}  // namespace
