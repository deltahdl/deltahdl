// §9.4.5: Intra-assignment timing controls

#include <gtest/gtest.h>

#include <cstdint>

uint64_t EvaluateRepeatCount(int64_t count, bool is_signed, bool is_unknown,
                             bool is_highz) {
  if (is_unknown || is_highz)
    return 0;
  if (is_signed && count <= 0)
    return 0;
  if (!is_signed && count < 0)
    return static_cast<uint64_t>(count);
  return static_cast<uint64_t>(count);
}

namespace {

TEST(TimingControl, RepeatCountZeroNoRepeat) {
  EXPECT_EQ(EvaluateRepeatCount(0, true, false, false), 0u);
}

TEST(TimingControl, RepeatCountNegativeSignedNoRepeat) {
  EXPECT_EQ(EvaluateRepeatCount(-3, true, false, false), 0u);
}

TEST(TimingControl, RepeatCountUnknownNoRepeat) {
  EXPECT_EQ(EvaluateRepeatCount(0, false, true, false), 0u);
}

TEST(TimingControl, RepeatCountHighZNoRepeat) {
  EXPECT_EQ(EvaluateRepeatCount(0, false, false, true), 0u);
}

TEST(TimingControl, RepeatCountPositivePassesThrough) {
  EXPECT_EQ(EvaluateRepeatCount(5, true, false, false), 5u);
}

TEST(TimingControl, RepeatCountNegativeUnsignedExecutes) {
  uint64_t result = EvaluateRepeatCount(-3, false, false, false);
  EXPECT_GT(result, 0u);
}

} // namespace
