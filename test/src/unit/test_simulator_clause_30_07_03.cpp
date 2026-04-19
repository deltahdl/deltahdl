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

// §30.7.3: an SDF pulse-limit annotation writes its reject/error values into
// every transition slot of the target path.
TEST(SdfPulseLimitAnnotation, BothLimitsAppliedAcrossAllSlots) {
  PathDelay pd = MakePathWithUniformDelay(40);
  ApplySdfPulseLimits(pd, /*reject=*/5, /*has_error=*/true, /*error=*/12);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 5u);
    EXPECT_EQ(pd.error_limit[i], 12u);
  }
}

// §30.7.3: when the SDF annotation lists only a reject limit, the helper
// mirrors that value into the error slot so a well-formed X band is still
// observable downstream.
TEST(SdfPulseLimitAnnotation, RejectOnlyMirrorsToError) {
  PathDelay pd = MakePathWithUniformDelay(40);
  ApplySdfPulseLimits(pd, /*reject=*/6, /*has_error=*/false, /*error=*/0);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 6u);
    EXPECT_EQ(pd.error_limit[i], 6u);
  }
}

// §30.7.3: SDF annotation targets pulse limits only — the propagation delays
// remain the responsibility of §30.5 mechanisms.
TEST(SdfPulseLimitAnnotation, PropagationDelaysPreserved) {
  PathDelay pd = MakePathWithUniformDelay(40);
  ApplySdfPulseLimits(pd, /*reject=*/3, /*has_error=*/true, /*error=*/9);
  for (int i = 0; i < 12; ++i) EXPECT_EQ(pd.delays[i], 40u);
}

// §30.7.3 precedence: when a PATHPULSE$ override is also present for the
// same path, applying SDF last overwrites the PATHPULSE$ values.
TEST(SdfPulseLimitAnnotation, SdfOverridesPathpulseValues) {
  PathDelay pd = MakePathWithUniformDelay(40);
  ApplyPulseControlOverride(pd, /*reject=*/2, /*has_error=*/true, /*error=*/7);
  ApplySdfPulseLimits(pd, /*reject=*/11, /*has_error=*/true, /*error=*/13);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 11u);
    EXPECT_EQ(pd.error_limit[i], 13u);
  }
}

// §30.7.3 precedence: global invocation-option limits must also lose to SDF
// annotation applied afterward.
TEST(SdfPulseLimitAnnotation, SdfOverridesGlobalInvocationLimits) {
  PathDelay pd = MakePathWithUniformDelay(100);
  ApplyGlobalPulseLimits(pd, /*reject_pct=*/50, /*error_pct=*/75);
  ApplySdfPulseLimits(pd, /*reject=*/4, /*has_error=*/true, /*error=*/8);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 4u);
    EXPECT_EQ(pd.error_limit[i], 8u);
  }
}

// §30.7.3 precedence: with all three mechanisms present (global, PATHPULSE$,
// SDF), SDF annotation is the final authority on every slot.
TEST(SdfPulseLimitAnnotation, SdfWinsOverGlobalAndPathpulseCombined) {
  PathDelay pd = MakePathWithUniformDelay(100);
  ApplyGlobalPulseLimits(pd, /*reject_pct=*/20, /*error_pct=*/80);
  ApplyPulseControlOverride(pd, /*reject=*/3, /*has_error=*/true, /*error=*/6);
  ApplySdfPulseLimits(pd, /*reject=*/17, /*has_error=*/true, /*error=*/23);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 17u);
    EXPECT_EQ(pd.error_limit[i], 23u);
  }
}

}  // namespace
