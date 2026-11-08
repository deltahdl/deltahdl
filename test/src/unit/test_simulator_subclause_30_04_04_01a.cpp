#include <gtest/gtest.h>

#include "common/types.h"
#include "simulator/specify_path_delay.h"

using namespace delta;

namespace {

constexpr Logic4Word kBit0{0, 0};
constexpr Logic4Word kBit1{1, 0};
constexpr Logic4Word kBitX{0, 1};
constexpr Logic4Word kBitZ{1, 1};

TEST(StateDependentPathCondition, TrueEnablesPath) {
  EXPECT_TRUE(StateDependentPathConditionEnables(kBit1));
}

TEST(StateDependentPathCondition, FalseDisablesPath) {
  EXPECT_FALSE(StateDependentPathConditionEnables(kBit0));
}

TEST(StateDependentPathCondition, UnknownIsTreatedAsTrue) {
  EXPECT_TRUE(StateDependentPathConditionEnables(kBitX));
  EXPECT_TRUE(StateDependentPathConditionEnables(kBitZ));
}

TEST(StateDependentPathCondition, MultiBitUsesLeastSignificantBit) {
  EXPECT_FALSE(StateDependentPathConditionEnables(Logic4Word{0b10, 0}));
  EXPECT_TRUE(StateDependentPathConditionEnables(Logic4Word{0b11, 0}));
}

}  // namespace
