#include "simulator/specify.h"

#include <gtest/gtest.h>

#include <cstdint>
#include <limits>

using namespace delta;

namespace {

TEST(MixedPathDistributedDelay, ModulePathLargerWinsLrmExample1) {
  EXPECT_EQ(SelectEffectivePathDelay( 22,
                                     1),
            22u);
}

TEST(MixedPathDistributedDelay, DistributedSumLargerWinsLrmExample2) {
  EXPECT_EQ(SelectEffectivePathDelay( 22,
                                     30),
            30u);
}

TEST(MixedPathDistributedDelay, EqualDelaysReturnThatValue) {
  EXPECT_EQ(SelectEffectivePathDelay(15, 15), 15u);
}

TEST(MixedPathDistributedDelay, ZeroModulePathReturnsDistributedSum) {
  EXPECT_EQ(SelectEffectivePathDelay(0, 9), 9u);
}

TEST(MixedPathDistributedDelay, ZeroDistributedSumReturnsModulePath) {
  EXPECT_EQ(SelectEffectivePathDelay(7, 0), 7u);
}

TEST(MixedPathDistributedDelay, BothZeroReturnsZero) {
  EXPECT_EQ(SelectEffectivePathDelay(0, 0), 0u);
}

TEST(MixedPathDistributedDelay, RuleIsSymmetricInOperandOrder) {
  EXPECT_EQ(SelectEffectivePathDelay(3, 8), 8u);
  EXPECT_EQ(SelectEffectivePathDelay(8, 3), 8u);
}

TEST(MixedPathDistributedDelay, LargeValuesCompareWithoutTruncation) {
  constexpr uint64_t big = std::numeric_limits<uint64_t>::max();
  EXPECT_EQ(SelectEffectivePathDelay(big, big - 1), big);
  EXPECT_EQ(SelectEffectivePathDelay(big - 1, big), big);
}

}
