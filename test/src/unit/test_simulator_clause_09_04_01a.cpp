// §9.4.1: Delay control

#include <gtest/gtest.h>

#include <cstdint>

uint64_t EvaluateDelay(int64_t value, bool is_unknown, bool is_highz) {
  if (is_unknown || is_highz)
    return 0;
  if (value < 0)
    return static_cast<uint64_t>(value);
  return static_cast<uint64_t>(value);
}

namespace {

TEST(TimingControl, UnknownDelayTreatedAsZero) {
  EXPECT_EQ(EvaluateDelay(0, true, false), 0u);
}

TEST(TimingControl, HighZDelayTreatedAsZero) {
  EXPECT_EQ(EvaluateDelay(0, false, true), 0u);
}

TEST(TimingControl, NegativeDelayUnsignedInterpretation) {
  uint64_t result = EvaluateDelay(-1, false, false);
  EXPECT_GT(result, 0u);
}

TEST(TimingControl, PositiveDelayPassesThrough) {
  EXPECT_EQ(EvaluateDelay(10, false, false), 10u);
}

TEST(TimingControl, ZeroDelayIsZero) {
  EXPECT_EQ(EvaluateDelay(0, false, false), 0u);
}

} // namespace
