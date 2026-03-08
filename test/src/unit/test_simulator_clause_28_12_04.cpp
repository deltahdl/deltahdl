#include <gtest/gtest.h>

#include "model_strength.h"

namespace {

TEST(WiredLogic, WiredAndSameStrength) {
  StrengthSignal strong_one{Val4::kV1, StrengthLevel::kHighz,
                            StrengthLevel::kStrong};
  StrengthSignal strong_zero{Val4::kV0, StrengthLevel::kStrong,
                             StrengthLevel::kHighz};
  auto result =
      CombineWithWiredLogic(strong_one, strong_zero, WiredLogicKind::kAnd);
  EXPECT_EQ(result.value, Val4::kV0);
}

TEST(WiredLogic, WiredOrSameStrength) {
  StrengthSignal strong_one{Val4::kV1, StrengthLevel::kHighz,
                            StrengthLevel::kStrong};
  StrengthSignal strong_zero{Val4::kV0, StrengthLevel::kStrong,
                             StrengthLevel::kHighz};
  auto result =
      CombineWithWiredLogic(strong_one, strong_zero, WiredLogicKind::kOr);
  EXPECT_EQ(result.value, Val4::kV1);
}

TEST(WiredLogic, WiredAndBothOne) {
  StrengthSignal a{Val4::kV1, StrengthLevel::kHighz, StrengthLevel::kPull};
  StrengthSignal b{Val4::kV1, StrengthLevel::kHighz, StrengthLevel::kPull};
  auto result = CombineWithWiredLogic(a, b, WiredLogicKind::kAnd);
  EXPECT_EQ(result.value, Val4::kV1);
}

TEST(WiredLogic, WiredOrBothZero) {
  StrengthSignal a{Val4::kV0, StrengthLevel::kPull, StrengthLevel::kHighz};
  StrengthSignal b{Val4::kV0, StrengthLevel::kPull, StrengthLevel::kHighz};
  auto result = CombineWithWiredLogic(a, b, WiredLogicKind::kOr);
  EXPECT_EQ(result.value, Val4::kV0);
}

}
