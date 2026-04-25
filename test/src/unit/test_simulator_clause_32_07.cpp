#include <gtest/gtest.h>

#include <string>

#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// =============================================================================
// §32.7 — Pulse limit annotation
// =============================================================================

// §32.7 sentence 1 + sentence 2: when the pulse-limit invocation
// percentages are left at their 100/100 default, the SDF annotator's
// default reject and error slots for an IOPATH delay must mirror the
// freshly installed propagation delay. The "by default, these limits
// are 100%" half of the rule is observable here — a regression that
// changed the default percentage to anything else would shift the
// installed limits away from the propagation delay and fail this
// test, so the annotator-level observation also pins the storage
// default in place.
TEST(SdfPulseLimitAnnotation,
     IopathDelayDefaultsToFullDelayWithDefaultPercentages) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;
  pre.delays[0] = 1;
  mgr.AddPathDelay(pre);

  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH A Z (5))))))
  )", file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.delays[0], 5u);
  EXPECT_EQ(pd.reject_limit[0], 5u);
  EXPECT_EQ(pd.error_limit[0], 5u);
}

// §32.7 sentence 2 + sentence 3: with the reject percentage set to 40
// and the error percentage to 80 via the pulse-limit invocation
// options, an IOPATH supplying a single delay value of 5 must
// annotate delay=5, reject=2, error=4. Pins down the per-component
// scaling rule: each percentage scales the propagation delay into
// the matching reject or error limit independently.
TEST(SdfPulseLimitAnnotation,
     CustomPercentagesScaleIopathDelayIntoRejectAndErrorLimits) {
  SpecifyManager mgr;
  mgr.SetGlobalPulseLimitPercents(/*reject_pct=*/40, /*error_pct=*/80);
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;
  pre.delays[0] = 1;
  mgr.AddPathDelay(pre);

  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH A Z (5))))))
  )", file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.delays[0], 5u);
  EXPECT_EQ(pd.reject_limit[0], 2u);
  EXPECT_EQ(pd.error_limit[0], 4u);
}

// §32.7 paragraph 4 ("the following annotation results in a delay of
// 5 and pulse limits of 0"): the extended IOPATH form `((5) () ())`
// supplies a delay value but leaves both reject and error slots empty,
// which the LRM defines as "hold the current values of the pulse
// limits". With the matched path's pulse limits originally at 0, the
// delay annotation must land on the propagation slot while the
// existing zeroes survive the overwrite. Exercises the LRM's worked
// example for the empty-pulse-limit-slots half of §32.7.
TEST(SdfPulseLimitAnnotation,
     ExtendedIopathWithEmptyPulseSlotsPreservesOriginalZeroLimits) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;
  pre.delays[0] = 0;
  pre.reject_limit[0] = 0;
  pre.error_limit[0] = 0;
  mgr.AddPathDelay(pre);

  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH A Z ((5) () ()))))))
  )", file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.delays[0], 5u);
  EXPECT_EQ(pd.reject_limit[0], 0u);
  EXPECT_EQ(pd.error_limit[0], 0u);
}

// §32.7 last sentence: "When PATHPULSE sets the pulse limits to values
// greater than the delay, SystemVerilog shall exhibit the same behavior
// as if the pulse limits had been set equal to the delay." With a path
// whose delay is 35 and a PATHPULSE attempting reject=50 and error=90,
// both limits exceed the delay and must be clamped down to 35 — the
// per-slot effective limit can never outrun the propagation slot it
// guards.
TEST(SdfPulseLimitAnnotation, PathpulseClampsLimitsExceedingDelay) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;
  pre.delays[0] = 35;
  pre.reject_limit[0] = 35;
  pre.error_limit[0] = 35;
  mgr.AddPathDelay(pre);

  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (PATHPULSE A Z (50) (90))))))
  )", file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.delays[0], 35u);
  EXPECT_EQ(pd.reject_limit[0], 35u);
  EXPECT_EQ(pd.error_limit[0], 35u);
}

// §32.7 last sentence, mixed clamping case: with a per-slot delay of
// 35, a PATHPULSE supplying reject=20 and error=90 must keep the
// reject value (already <= delay) untouched while clamping only the
// error value down to 35. Pins down that the clamp is per-slot and
// per-component, not an all-or-nothing decision — a correctly clamped
// implementation must distinguish the two limits and act on each
// independently.
TEST(SdfPulseLimitAnnotation, PathpulseClampsOnlyTheLimitsThatExceedDelay) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;
  pre.delays[0] = 35;
  pre.reject_limit[0] = 35;
  pre.error_limit[0] = 35;
  mgr.AddPathDelay(pre);

  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (PATHPULSE A Z (20) (90))))))
  )", file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.reject_limit[0], 20u);
  EXPECT_EQ(pd.error_limit[0], 35u);
}

// §32.7 paragraph 5 ("There are two SDF constructs that annotate only
// to pulse limits, PATHPULSE and PATHPULSEPERCENT. They do not affect
// the delay."): a PATHPULSE annotation must leave the matched
// PathDelay's `delays` array exactly as it was. Combined with the
// value-clamp tests above, this pins down both halves of the
// pulse-limit-only contract holding simultaneously — the propagation
// slot stays at 35 even when the PATHPULSE values themselves are
// clipped against it.
TEST(SdfPulseLimitAnnotation, PathpulseLeavesPropagationDelaysUntouched) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;
  pre.delays[0] = 35;
  mgr.AddPathDelay(pre);

  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (PATHPULSE A Z (10) (20))))))
  )", file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  EXPECT_EQ(mgr.GetPathDelays()[0].delays[0], 35u);
}

// §32.7 paragraph 5 companion on PATHPULSEPERCENT: the percent form
// also annotates only to pulse limits — the matched path's
// propagation delays must survive a PATHPULSEPERCENT entry untouched.
// Pairs with the PATHPULSE-leaves-delays test above so both rows of
// Table 32-1 are covered; an implementation that special-cased only
// PATHPULSE would pass the other test while letting PATHPULSEPERCENT
// quietly mutate `delays`.
TEST(SdfPulseLimitAnnotation,
     PathpulsepercentLeavesPropagationDelaysUntouched) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;
  pre.delays[0] = 50;
  mgr.AddPathDelay(pre);

  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (PATHPULSEPERCENT A Z (25) (75))))))
  )", file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  EXPECT_EQ(mgr.GetPathDelays()[0].delays[0], 50u);
}

// §32.7 paragraph 4 (negative-result clamp): "Annotations in
// INCREMENT mode can result in pulse limits less than 0, in which
// case they shall be adjusted to 0." With a path's reject and error
// limits both at 3, a signed INCREMENT delta of (-4) / (-5) drives
// both limits below zero and must be clamped to zero per the rule.
// The original limits and deltas are exactly the ones the LRM's
// worked example uses.
TEST(SdfPulseLimitAnnotation,
     IncrementPulseLimitClampsNegativeResultToZero) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;
  for (int i = 0; i < 12; ++i) {
    pre.delays[i] = 10;
    pre.reject_limit[i] = 3;
    pre.error_limit[i] = 3;
  }
  mgr.AddPathDelay(pre);

  mgr.IncrementSdfPulseLimit("A", "Z", /*reject_delta=*/-4,
                             /*has_error=*/true, /*error_delta=*/-5);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 0u);
    EXPECT_EQ(pd.error_limit[i], 0u);
  }
}

// §32.7 paragraph 4 boundary case: a non-negative INCREMENT delta
// must pass through unclamped — the clamp-to-zero rule fires only
// when the addition would yield a negative value. With original
// limits both at 3 and a +2 / +4 delta, the post-increment limits
// sit at 5 / 7. Pins down that the clamp is conditional on the
// negative result and not unconditional.
TEST(SdfPulseLimitAnnotation,
     IncrementPulseLimitAccumulatesPositiveDeltaWithoutClamping) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;
  for (int i = 0; i < 12; ++i) {
    pre.delays[i] = 10;
    pre.reject_limit[i] = 3;
    pre.error_limit[i] = 3;
  }
  mgr.AddPathDelay(pre);

  mgr.IncrementSdfPulseLimit("A", "Z", /*reject_delta=*/2,
                             /*has_error=*/true, /*error_delta=*/4);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.reject_limit[0], 5u);
  EXPECT_EQ(pd.error_limit[0], 7u);
}

// §32.7 paragraph 4 + §30.7.3 single-vs-paired-value rule: when the
// INCREMENT entry omits the error delta, the reject delta carries
// across so the X band remains well-formed. With original limits both
// at 1 and a (-3) reject delta with no error supplied, both
// post-increment limits drop below zero and clamp to 0. Pins down
// that the mirror rule applies before the clamp, not after — a
// reject-only INCREMENT with mirror-after-clamp would yield (0,
// reject_clamped) instead of (0, 0).
TEST(SdfPulseLimitAnnotation,
     IncrementPulseLimitMirrorsRejectIntoErrorBeforeClamping) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;
  for (int i = 0; i < 12; ++i) {
    pre.delays[i] = 10;
    pre.reject_limit[i] = 1;
    pre.error_limit[i] = 1;
  }
  mgr.AddPathDelay(pre);

  mgr.IncrementSdfPulseLimit("A", "Z", /*reject_delta=*/-3,
                             /*has_error=*/false, /*error_delta=*/0);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.reject_limit[0], 0u);
  EXPECT_EQ(pd.error_limit[0], 0u);
}

// §32.7 last sentence, per-slot edge case: each transition slot guards
// its own propagation delay, so a PATHPULSE that exceeds the slot 0
// delay but fits within the slot 1 delay must clamp slot 0 while
// leaving slot 1 alone. With delays[0]=20 and delays[1]=80, a
// PATHPULSE supplying reject=50 and error=60 must produce
// reject_limit[0]=20 / error_limit[0]=20 (both clamped against the
// narrower slot-0 delay) and reject_limit[1]=50 / error_limit[1]=60
// (both within the wider slot-1 delay). Forecloses an implementation
// that compares against a single global delay value rather than the
// per-slot one.
TEST(SdfPulseLimitAnnotation, PathpulseClampsPerSlotAgainstEachSlotsDelay) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 2;
  pre.delays[0] = 20;
  pre.delays[1] = 80;
  pre.reject_limit[0] = 20;
  pre.reject_limit[1] = 80;
  pre.error_limit[0] = 20;
  pre.error_limit[1] = 80;
  mgr.AddPathDelay(pre);

  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (PATHPULSE A Z (50) (60))))))
  )", file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.reject_limit[0], 20u);
  EXPECT_EQ(pd.error_limit[0], 20u);
  EXPECT_EQ(pd.reject_limit[1], 50u);
  EXPECT_EQ(pd.error_limit[1], 60u);
}

// §32.7 paragraph 4, per-component edge case: the clamp-to-zero rule
// fires only on components that would actually go negative. With
// original limits both at 3 and a delta of (reject=-5, error=+2),
// only the reject component would land below zero — the error
// component stays at the post-add value of 5. Forecloses an
// implementation that clamps both components together whenever any
// component goes negative.
TEST(SdfPulseLimitAnnotation,
     IncrementPulseLimitClampsOnlyComponentsThatGoNegative) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;
  for (int i = 0; i < 12; ++i) {
    pre.delays[i] = 10;
    pre.reject_limit[i] = 3;
    pre.error_limit[i] = 3;
  }
  mgr.AddPathDelay(pre);

  mgr.IncrementSdfPulseLimit("A", "Z", /*reject_delta=*/-5,
                             /*has_error=*/true, /*error_delta=*/2);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.reject_limit[0], 0u);
  EXPECT_EQ(pd.error_limit[0], 5u);
}

// §32.7 sentence 2 boundary: the invocation-option percentages can be
// modified to any value, including the lower bound of 0. With both
// percentages set to 0, an SDF IOPATH delay annotation must produce
// pulse limits of zero on every transition slot — the percentage
// scaling is genuinely consulted instead of bypassed when the values
// are at an extreme. Pins down that the SetGlobalPulseLimitPercents
// path is wired through the annotator for non-default values rather
// than falling back to the inertial default whenever the percentages
// are unusual.
TEST(SdfPulseLimitAnnotation,
     ZeroPercentSettingsProduceZeroPulseLimitsForIopath) {
  SpecifyManager mgr;
  mgr.SetGlobalPulseLimitPercents(/*reject_pct=*/0, /*error_pct=*/0);
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;
  pre.delays[0] = 1;
  mgr.AddPathDelay(pre);

  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH A Z (10))))))
  )", file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.delays[0], 10u);
  EXPECT_EQ(pd.reject_limit[0], 0u);
  EXPECT_EQ(pd.error_limit[0], 0u);
}

}  // namespace
