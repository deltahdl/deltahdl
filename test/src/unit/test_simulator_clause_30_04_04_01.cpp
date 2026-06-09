#include "simulator/specify.h"

#include <gtest/gtest.h>

#include "common/types.h"

using namespace delta;

namespace {

constexpr Logic4Word kBit0{0, 0};
constexpr Logic4Word kBit1{1, 0};
constexpr Logic4Word kBitX{0, 1};
constexpr Logic4Word kBitZ{1, 1};

// §30.4.4.1: a state-dependent path is assigned its delay only when the
// conditional expression evaluates to true (1).
TEST(StateDependentPathCondition, TrueEnablesPath) {
  EXPECT_TRUE(StateDependentPathConditionEnables(kBit1));
}

TEST(StateDependentPathCondition, FalseDisablesPath) {
  EXPECT_FALSE(StateDependentPathConditionEnables(kBit0));
}

// §30.4.4.1: an x or z result is treated as true.
TEST(StateDependentPathCondition, UnknownIsTreatedAsTrue) {
  EXPECT_TRUE(StateDependentPathConditionEnables(kBitX));
  EXPECT_TRUE(StateDependentPathConditionEnables(kBitZ));
}

// §30.4.4.1: a multi-bit result is represented by its LSB. Higher-order bits do
// not affect the decision.
TEST(StateDependentPathCondition, MultiBitUsesLeastSignificantBit) {
  // LSB clear, higher bit set -> path inactive.
  EXPECT_FALSE(StateDependentPathConditionEnables(Logic4Word{0b10, 0}));
  // LSB set, higher bit set -> path active.
  EXPECT_TRUE(StateDependentPathConditionEnables(Logic4Word{0b11, 0}));
}

}  // namespace
