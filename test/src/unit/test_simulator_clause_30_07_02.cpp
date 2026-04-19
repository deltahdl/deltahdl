#include <gtest/gtest.h>

#include "simulator/specify.h"

using namespace delta;

namespace {

PathDelay MakePathWithUniformDelay(uint64_t value) {
  PathDelay pd;
  pd.delay_count = 1;
  for (int i = 0; i < 12; ++i) pd.delays[i] = value;
  InitDefaultPulseLimits(pd);
  return pd;
}

// §30.7.2: 100% applied to every delay leaves the limits equal to the delays
// themselves, matching the "no invocation option present" fallback.
TEST(GlobalPulseLimitScaling, HundredPercentEqualsInertialDefault) {
  PathDelay pd = MakePathWithUniformDelay(40);
  ApplyGlobalPulseLimits(pd, /*reject_pct=*/100, /*error_pct=*/100);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 40u);
    EXPECT_EQ(pd.error_limit[i], 40u);
  }
}

// §30.7.2: the reject-limit invocation option scales transition delays into
// reject limits across every slot.
TEST(GlobalPulseLimitScaling, RejectPercentageScalesAllSlots) {
  PathDelay pd = MakePathWithUniformDelay(40);
  ApplyGlobalPulseLimits(pd, /*reject_pct=*/25, /*error_pct=*/100);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 10u);
    EXPECT_EQ(pd.error_limit[i], 40u);
  }
}

// §30.7.2: the error-limit invocation option scales transition delays into
// error limits across every slot.
TEST(GlobalPulseLimitScaling, ErrorPercentageScalesAllSlots) {
  PathDelay pd = MakePathWithUniformDelay(40);
  ApplyGlobalPulseLimits(pd, /*reject_pct=*/25, /*error_pct=*/75);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 10u);
    EXPECT_EQ(pd.error_limit[i], 30u);
  }
}

// §30.7.2: 0% is the lower bound of the legal percentage range and produces
// zero limits everywhere.
TEST(GlobalPulseLimitScaling, ZeroPercentProducesZeroLimits) {
  PathDelay pd = MakePathWithUniformDelay(40);
  ApplyGlobalPulseLimits(pd, /*reject_pct=*/0, /*error_pct=*/0);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 0u);
    EXPECT_EQ(pd.error_limit[i], 0u);
  }
}

// §30.7.2: when the error percentage is smaller than the reject percentage,
// the error percentage is silently raised to the reject percentage rather
// than producing an invalid X band.
TEST(GlobalPulseLimitScaling, ErrorBelowRejectIsClampedUp) {
  PathDelay pd = MakePathWithUniformDelay(100);
  ApplyGlobalPulseLimits(pd, /*reject_pct=*/60, /*error_pct=*/30);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 60u);
    EXPECT_EQ(pd.error_limit[i], 60u);
  }
}

// §30.7.2: scaling is per-slot — heterogeneous transition delays each get
// their own scaled limit rather than sharing one computed value.
TEST(GlobalPulseLimitScaling, PerSlotScalingIndependent) {
  PathDelay pd;
  pd.delay_count = 12;
  for (int i = 0; i < 12; ++i) pd.delays[i] = static_cast<uint64_t>(i + 1) * 10;
  InitDefaultPulseLimits(pd);
  ApplyGlobalPulseLimits(pd, /*reject_pct=*/50, /*error_pct=*/100);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], static_cast<uint64_t>(i + 1) * 5);
    EXPECT_EQ(pd.error_limit[i], static_cast<uint64_t>(i + 1) * 10);
  }
}

// §30.7.2: when a PATHPULSE$ override follows a global-pulse-limit
// application, the PATHPULSE$ values shall take precedence for that path.
TEST(GlobalPulseLimitScaling, PathpulseOverridesGlobalLimits) {
  PathDelay pd = MakePathWithUniformDelay(100);
  ApplyGlobalPulseLimits(pd, /*reject_pct=*/50, /*error_pct=*/80);
  ApplyPulseControlOverride(pd, /*reject=*/5, /*has_error=*/true, /*error=*/9);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 5u);
    EXPECT_EQ(pd.error_limit[i], 9u);
  }
}

// §30.7.2: the scaling step operates on pulse limits only — the underlying
// transition delays in `delays` belong to §30.5 and must be left untouched.
TEST(GlobalPulseLimitScaling, PropagationDelaysPreserved) {
  PathDelay pd = MakePathWithUniformDelay(40);
  ApplyGlobalPulseLimits(pd, /*reject_pct=*/50, /*error_pct=*/70);
  for (int i = 0; i < 12; ++i) EXPECT_EQ(pd.delays[i], 40u);
}

}  // namespace
