// §28.12.4: Wired logic net types

#include <gtest/gtest.h>

#include "model_strength.h"

namespace {

// =============================================================
// §28.12.4: Wired logic net types
// =============================================================
// §28.12.4: "triand, wand ... shall resolve conflicts when multiple
//  drivers have the same strength. ... treating signals as inputs
//  of logic functions."
// Wired AND: 1 AND 0 = 0
TEST(WiredLogic, WiredAndSameStrength) {
  StrengthSignal strong_one{Val4::kV1, StrengthLevel::kHighz,
                            StrengthLevel::kStrong};
  StrengthSignal strong_zero{Val4::kV0, StrengthLevel::kStrong,
                             StrengthLevel::kHighz};
  auto result =
      CombineWithWiredLogic(strong_one, strong_zero, WiredLogicKind::kAnd);
  EXPECT_EQ(result.value, Val4::kV0);
}

// Wired OR: 1 OR 0 = 1
TEST(WiredLogic, WiredOrSameStrength) {
  StrengthSignal strong_one{Val4::kV1, StrengthLevel::kHighz,
                            StrengthLevel::kStrong};
  StrengthSignal strong_zero{Val4::kV0, StrengthLevel::kStrong,
                             StrengthLevel::kHighz};
  auto result =
      CombineWithWiredLogic(strong_one, strong_zero, WiredLogicKind::kOr);
  EXPECT_EQ(result.value, Val4::kV1);
}

// Wired AND: both 1 = 1
TEST(WiredLogic, WiredAndBothOne) {
  StrengthSignal a{Val4::kV1, StrengthLevel::kHighz, StrengthLevel::kPull};
  StrengthSignal b{Val4::kV1, StrengthLevel::kHighz, StrengthLevel::kPull};
  auto result = CombineWithWiredLogic(a, b, WiredLogicKind::kAnd);
  EXPECT_EQ(result.value, Val4::kV1);
}

// Wired OR: both 0 = 0
TEST(WiredLogic, WiredOrBothZero) {
  StrengthSignal a{Val4::kV0, StrengthLevel::kPull, StrengthLevel::kHighz};
  StrengthSignal b{Val4::kV0, StrengthLevel::kPull, StrengthLevel::kHighz};
  auto result = CombineWithWiredLogic(a, b, WiredLogicKind::kOr);
  EXPECT_EQ(result.value, Val4::kV0);
}

}  // namespace
