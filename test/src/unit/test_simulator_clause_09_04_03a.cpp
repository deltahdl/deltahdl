// Non-LRM tests

#include <gtest/gtest.h>
#include <cstdint>

bool EvaluateWaitCondition(uint64_t value) { return value != 0; }

namespace {

TEST(TimingControl, WaitConditionNonzeroIsTrue) {
  EXPECT_TRUE(EvaluateWaitCondition(42));
}

}  // namespace
