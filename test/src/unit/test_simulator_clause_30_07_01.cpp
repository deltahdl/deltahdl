#include <gtest/gtest.h>

#include "simulator/specify.h"

using namespace delta;

namespace {

PathDelay MakePathWithDelays(uint64_t value) {
  PathDelay pd;
  pd.delay_count = 1;
  for (int i = 0; i < 12; ++i) pd.delays[i] = value;
  InitDefaultPulseLimits(pd);
  return pd;
}

TEST(ApplyPulseControlOverride, RejectOnlyMirrorsErrorAcrossAllSlots) {
  PathDelay pd = MakePathWithDelays(10);
  ApplyPulseControlOverride(pd, 3, false, 0);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 3u);
    EXPECT_EQ(pd.error_limit[i], 3u);
  }
}

TEST(ApplyPulseControlOverride, BothLimitsAppliedAcrossAllSlots) {
  PathDelay pd = MakePathWithDelays(10);
  ApplyPulseControlOverride(pd, 2, true, 7);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 2u);
    EXPECT_EQ(pd.error_limit[i], 7u);
  }
}

TEST(ApplyPulseControlOverride, PreservesPropagationDelays) {
  PathDelay pd = MakePathWithDelays(10);
  ApplyPulseControlOverride(pd, 4, true, 8);
  for (int i = 0; i < 12; ++i) EXPECT_EQ(pd.delays[i], 10u);
}

}
