#include "simulator/specify.h"

#include <gtest/gtest.h>

#include <cstdint>
#include <limits>

using namespace delta;

namespace {

// §30.6 Example 1 (Figure 30-3): the module path from D to Q is 22, while
// the distributed gates along the same path sum to 0 + 1 = 1. The runtime
// must pick the larger of the two, so the effective delay on Q is 22.
TEST(MixedPathDistributedDelay, ModulePathLargerWinsLrmExample1) {
  EXPECT_EQ(SelectEffectivePathDelay(/*module_path=*/22,
                                     /*distributed_sum=*/1),
            22u);
}

// §30.6 Example 2 (Figure 30-4): the module path from D to Q is 22, while
// the distributed gates along the same path sum to 10 + 20 = 30. The
// effective delay is the distributed sum of 30.
TEST(MixedPathDistributedDelay, DistributedSumLargerWinsLrmExample2) {
  EXPECT_EQ(SelectEffectivePathDelay(/*module_path=*/22,
                                     /*distributed_sum=*/30),
            30u);
}

// §30.6: when both delays are identical, "larger of the two" reduces to the
// shared value, so the selector must return it unchanged rather than
// doubling or zeroing.
TEST(MixedPathDistributedDelay, EqualDelaysReturnThatValue) {
  EXPECT_EQ(SelectEffectivePathDelay(15, 15), 15u);
}

// §30.6 edge case: a module without a matching specify-block path delay
// contributes a zero module-path term, so the selector must fall back to
// the distributed sum unchanged.
TEST(MixedPathDistributedDelay, ZeroModulePathReturnsDistributedSum) {
  EXPECT_EQ(SelectEffectivePathDelay(0, 9), 9u);
}

// §30.6 edge case: a module with no primitive instances between source and
// destination (distributed sum = 0) must still honor the module path delay
// as the larger term.
TEST(MixedPathDistributedDelay, ZeroDistributedSumReturnsModulePath) {
  EXPECT_EQ(SelectEffectivePathDelay(7, 0), 7u);
}

// §30.6 edge case: both delays zero means there is no scheduling delay at
// all, and the selector must report exactly zero rather than some sentinel.
TEST(MixedPathDistributedDelay, BothZeroReturnsZero) {
  EXPECT_EQ(SelectEffectivePathDelay(0, 0), 0u);
}

// §30.6: the max-of-two rule is symmetric in operand order. Swapping which
// side carries the larger value must not affect the outcome — both cases
// must yield the same larger value.
TEST(MixedPathDistributedDelay, RuleIsSymmetricInOperandOrder) {
  EXPECT_EQ(SelectEffectivePathDelay(3, 8), 8u);
  EXPECT_EQ(SelectEffectivePathDelay(8, 3), 8u);
}

// §30.6: the selector must not silently truncate large 64-bit values. At
// the top of the uint64_t range the larger of the two must still be
// selected faithfully.
TEST(MixedPathDistributedDelay, LargeValuesCompareWithoutTruncation) {
  constexpr uint64_t big = std::numeric_limits<uint64_t>::max();
  EXPECT_EQ(SelectEffectivePathDelay(big, big - 1), big);
  EXPECT_EQ(SelectEffectivePathDelay(big - 1, big), big);
}

}  // namespace
