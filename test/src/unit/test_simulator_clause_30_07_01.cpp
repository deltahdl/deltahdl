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

// §30.7.1: when PATHPULSE$ lists only a reject limit, the error limit takes
// the same value. The override helper must mirror reject to error across every
// transition slot so ClassifyPulse can never observe a narrower X band than
// the LRM mandates.
TEST(ApplyPulseControlOverride, RejectOnlyMirrorsErrorAcrossAllSlots) {
  PathDelay pd = MakePathWithDelays(10);
  ApplyPulseControlOverride(pd, /*reject=*/3, /*has_error=*/false, /*error=*/0);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 3u);
    EXPECT_EQ(pd.error_limit[i], 3u);
  }
}

// §30.7.1: when both limits are named, the override writes each limit into the
// matching slot across all 12 transition entries without further derivation.
TEST(ApplyPulseControlOverride, BothLimitsAppliedAcrossAllSlots) {
  PathDelay pd = MakePathWithDelays(10);
  ApplyPulseControlOverride(pd, /*reject=*/2, /*has_error=*/true, /*error=*/7);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 2u);
    EXPECT_EQ(pd.error_limit[i], 7u);
  }
}

// §30.7.1 governs pulse-filter limits only — the underlying propagation delays
// belong to §30.5 and must survive an override untouched.
TEST(ApplyPulseControlOverride, PreservesPropagationDelays) {
  PathDelay pd = MakePathWithDelays(10);
  ApplyPulseControlOverride(pd, /*reject=*/4, /*has_error=*/true, /*error=*/8);
  for (int i = 0; i < 12; ++i) EXPECT_EQ(pd.delays[i], 10u);
}

}  // namespace
