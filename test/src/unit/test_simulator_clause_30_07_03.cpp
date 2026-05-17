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

TEST(SdfPulseLimitAnnotation, BothLimitsAppliedAcrossAllSlots) {
  PathDelay pd = MakePathWithUniformDelay(40);
  ApplySdfPulseLimits(pd, 5, true, 12);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 5u);
    EXPECT_EQ(pd.error_limit[i], 12u);
  }
}

TEST(SdfPulseLimitAnnotation, RejectOnlyMirrorsToError) {
  PathDelay pd = MakePathWithUniformDelay(40);
  ApplySdfPulseLimits(pd, 6, false, 0);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 6u);
    EXPECT_EQ(pd.error_limit[i], 6u);
  }
}

TEST(SdfPulseLimitAnnotation, PropagationDelaysPreserved) {
  PathDelay pd = MakePathWithUniformDelay(40);
  ApplySdfPulseLimits(pd, 3, true, 9);
  for (int i = 0; i < 12; ++i) EXPECT_EQ(pd.delays[i], 40u);
}

TEST(SdfPulseLimitAnnotation, SdfOverridesPathpulseValues) {
  PathDelay pd = MakePathWithUniformDelay(40);
  ApplyPulseControlOverride(pd, 2, true, 7);
  ApplySdfPulseLimits(pd, 11, true, 13);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 11u);
    EXPECT_EQ(pd.error_limit[i], 13u);
  }
}

TEST(SdfPulseLimitAnnotation, SdfOverridesGlobalInvocationLimits) {
  PathDelay pd = MakePathWithUniformDelay(100);
  ApplyGlobalPulseLimits(pd, 50, 75);
  ApplySdfPulseLimits(pd, 4, true, 8);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 4u);
    EXPECT_EQ(pd.error_limit[i], 8u);
  }
}

TEST(SdfPulseLimitAnnotation, SdfWinsOverGlobalAndPathpulseCombined) {
  PathDelay pd = MakePathWithUniformDelay(100);
  ApplyGlobalPulseLimits(pd, 20, 80);
  ApplyPulseControlOverride(pd, 3, true, 6);
  ApplySdfPulseLimits(pd, 17, true, 23);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 17u);
    EXPECT_EQ(pd.error_limit[i], 23u);
  }
}

}
