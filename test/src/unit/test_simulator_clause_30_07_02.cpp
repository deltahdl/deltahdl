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

TEST(GlobalPulseLimitScaling, HundredPercentEqualsInertialDefault) {
  PathDelay pd = MakePathWithUniformDelay(40);
  ApplyGlobalPulseLimits(pd, 100, 100);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 40u);
    EXPECT_EQ(pd.error_limit[i], 40u);
  }
}

TEST(GlobalPulseLimitScaling, ErrorPercentageScalesAllSlots) {
  PathDelay pd = MakePathWithUniformDelay(40);
  ApplyGlobalPulseLimits(pd, 25, 75);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 10u);
    EXPECT_EQ(pd.error_limit[i], 30u);
  }
}

TEST(GlobalPulseLimitScaling, ZeroPercentProducesZeroLimits) {
  PathDelay pd = MakePathWithUniformDelay(40);
  ApplyGlobalPulseLimits(pd, 0, 0);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 0u);
    EXPECT_EQ(pd.error_limit[i], 0u);
  }
}

TEST(GlobalPulseLimitScaling, ErrorBelowRejectIsClampedUp) {
  PathDelay pd = MakePathWithUniformDelay(100);
  ApplyGlobalPulseLimits(pd, 60, 30);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 60u);
    EXPECT_EQ(pd.error_limit[i], 60u);
  }
}

TEST(GlobalPulseLimitScaling, PerSlotScalingIndependent) {
  PathDelay pd;
  pd.delay_count = 12;
  for (int i = 0; i < 12; ++i) pd.delays[i] = static_cast<uint64_t>(i + 1) * 10;
  InitDefaultPulseLimits(pd);
  ApplyGlobalPulseLimits(pd, 50, 100);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], static_cast<uint64_t>(i + 1) * 5);
    EXPECT_EQ(pd.error_limit[i], static_cast<uint64_t>(i + 1) * 10);
  }
}

TEST(GlobalPulseLimitScaling, PathpulseOverridesGlobalLimits) {
  PathDelay pd = MakePathWithUniformDelay(100);
  ApplyGlobalPulseLimits(pd, 50, 80);
  ApplyPulseControlOverride(pd, 5, true, 9);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 5u);
    EXPECT_EQ(pd.error_limit[i], 9u);
  }
}

TEST(GlobalPulseLimitScaling, DefaultGlobalPercentagesAreHundred) {
  // §30.7.2: when neither global invocation option is present, both the reject
  // and error limit percentages default to 100%.
  SpecifyManager mgr;
  EXPECT_EQ(mgr.RejectPulseLimitPercent(), 100u);
  EXPECT_EQ(mgr.ErrorPulseLimitPercent(), 100u);
}

TEST(GlobalPulseLimitScaling, PropagationDelaysPreserved) {
  PathDelay pd = MakePathWithUniformDelay(40);
  ApplyGlobalPulseLimits(pd, 50, 70);
  for (int i = 0; i < 12; ++i) EXPECT_EQ(pd.delays[i], 40u);
}

}  // namespace
