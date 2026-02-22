// §9.4.3: Level-sensitive event control

#include <gtest/gtest.h>

#include <cstdint>

bool EvaluateWaitCondition(uint64_t value) { return value != 0; }

namespace {

TEST(TimingControl, WaitConditionTrueUnblocks) {
  EXPECT_TRUE(EvaluateWaitCondition(1));
}

TEST(TimingControl, WaitConditionFalseBlocks) {
  EXPECT_FALSE(EvaluateWaitCondition(0));
}

TEST(TimingControl, WaitConditionNonzeroIsTrue) {
  EXPECT_TRUE(EvaluateWaitCondition(42));
}

}  // namespace
