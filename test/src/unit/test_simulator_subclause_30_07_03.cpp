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

// SDF precedence is a full replacement, not a partial merge: an annotation
// that carries only a reject value must mirror it onto the error limit and
// overwrite the distinct error limit a prior PATHPULSE$ override had set.
TEST(SdfPulseLimitAnnotation, SdfRejectOnlyFullyReplacesPriorPathpulseLimits) {
  PathDelay pd = MakePathWithUniformDelay(40);
  ApplyPulseControlOverride(pd, 9, true, 21);
  ApplySdfPulseLimits(pd, 5, false, 0);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 5u);
    EXPECT_EQ(pd.error_limit[i], 5u);
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

// §30.7.3: SDF annotation takes precedence, and precedence is not the order the
// three sources were applied in. Every case above applies the SDF values last,
// where a setter that simply wrote what it was given would agree with one that
// weighs the sources; applying a PATHPULSE$ override afterwards is what tells
// the two apart. The annotated values stand.
TEST(SdfPulseLimitAnnotation, PathpulseAppliedAfterSdfLeavesTheAnnotation) {
  PathDelay pd = MakePathWithUniformDelay(40);
  ApplySdfPulseLimits(pd, 11, true, 13);
  ApplyPulseControlOverride(pd, 2, true, 7);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 11u);
    EXPECT_EQ(pd.error_limit[i], 13u);
  }
}

// §30.7.3: the same of the global invocation options, which reach a path by a
// different setter and derive their limits from the delays rather than being
// given them.
TEST(SdfPulseLimitAnnotation, GlobalLimitsAppliedAfterSdfLeaveTheAnnotation) {
  PathDelay pd = MakePathWithUniformDelay(100);
  ApplySdfPulseLimits(pd, 4, true, 8);
  ApplyGlobalPulseLimits(pd, 50, 75);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 4u);
    EXPECT_EQ(pd.error_limit[i], 8u);
  }
}

// §30.7.2: a PATHPULSE$ specparam takes precedence over the global invocation
// options, which is the half of the ordering below SDF annotation. Applying the
// percentages after the specparam leaves the specparam's values.
TEST(SdfPulseLimitAnnotation, GlobalLimitsAppliedAfterPathpulseLeaveIt) {
  PathDelay pd = MakePathWithUniformDelay(100);
  ApplyPulseControlOverride(pd, 3, true, 6);
  ApplyGlobalPulseLimits(pd, 20, 80);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 3u);
    EXPECT_EQ(pd.error_limit[i], 6u);
  }
}

// §30.7.2: the global options do reach a path no other source has set, so the
// case above rejects the percentages for their standing rather than rejecting
// them always.
TEST(SdfPulseLimitAnnotation, GlobalLimitsReachAPathNoOtherSourceSet) {
  PathDelay pd = MakePathWithUniformDelay(100);
  ApplyGlobalPulseLimits(pd, 20, 80);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 20u);
    EXPECT_EQ(pd.error_limit[i], 80u);
  }
}

// §30.7.3 with all three sources applied in the order that most tests the
// ordering: the lowest precedence last. The annotated values stand whichever
// order the three arrive in, which is what makes the precedence a property of
// the sources rather than of the caller.
TEST(SdfPulseLimitAnnotation, SdfWinsWhateverOrderTheSourcesArriveIn) {
  PathDelay pd = MakePathWithUniformDelay(100);
  ApplySdfPulseLimits(pd, 17, true, 23);
  ApplyPulseControlOverride(pd, 3, true, 6);
  ApplyGlobalPulseLimits(pd, 20, 80);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 17u);
    EXPECT_EQ(pd.error_limit[i], 23u);
  }
}

}  // namespace
