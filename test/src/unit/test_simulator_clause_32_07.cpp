#include <gtest/gtest.h>

#include <string>

#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// Builds a manager seeded with a single-slot A->Z path delay (delays[0] = 1),
// optionally sets the global pulse-limit percentages, then parses and annotates
// an absolute IOPATH A Z (5) SDF cell. Fills `pd` with the resulting path
// delay.
static void AnnotateIopathFiveDelay(unsigned reject_pct, unsigned error_pct,
                                    bool set_percents, PathDelay& pd) {
  SpecifyManager mgr;
  if (set_percents) {
    mgr.SetGlobalPulseLimitPercents(reject_pct, error_pct);
  }
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
  )",
                       file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  pd = mgr.GetPathDelays()[0];
}

TEST(SdfPulseLimitAnnotation,
     IopathDelayDefaultsToFullDelayWithDefaultPercentages) {
  PathDelay pd;
  AnnotateIopathFiveDelay(0, 0, /*set_percents=*/false, pd);
  EXPECT_EQ(pd.delays[0], 5u);
  EXPECT_EQ(pd.reject_limit[0], 5u);
  EXPECT_EQ(pd.error_limit[0], 5u);
}

TEST(SdfPulseLimitAnnotation,
     CustomPercentagesScaleIopathDelayIntoRejectAndErrorLimits) {
  PathDelay pd;
  AnnotateIopathFiveDelay(40, 80, /*set_percents=*/true, pd);
  EXPECT_EQ(pd.delays[0], 5u);
  EXPECT_EQ(pd.reject_limit[0], 2u);
  EXPECT_EQ(pd.error_limit[0], 4u);
}

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
  )",
                       file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.delays[0], 5u);
  EXPECT_EQ(pd.reject_limit[0], 0u);
  EXPECT_EQ(pd.error_limit[0], 0u);
}

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
  )",
                       file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.delays[0], 35u);
  EXPECT_EQ(pd.reject_limit[0], 35u);
  EXPECT_EQ(pd.error_limit[0], 35u);
}

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
  )",
                       file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.reject_limit[0], 20u);
  EXPECT_EQ(pd.error_limit[0], 35u);
}

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
  )",
                       file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  EXPECT_EQ(mgr.GetPathDelays()[0].delays[0], 35u);
}

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
  )",
                       file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  EXPECT_EQ(mgr.GetPathDelays()[0].delays[0], 50u);
}

TEST(SdfPulseLimitAnnotation, IncrementPulseLimitClampsNegativeResultToZero) {
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

  mgr.IncrementSdfPulseLimit("A", "Z", -4, true, -5);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 0u);
    EXPECT_EQ(pd.error_limit[i], 0u);
  }
}

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

  mgr.IncrementSdfPulseLimit("A", "Z", -3, false, 0);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.reject_limit[0], 0u);
  EXPECT_EQ(pd.error_limit[0], 0u);
}

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
  )",
                       file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.reject_limit[0], 20u);
  EXPECT_EQ(pd.error_limit[0], 20u);
  EXPECT_EQ(pd.reject_limit[1], 50u);
  EXPECT_EQ(pd.error_limit[1], 60u);
}

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

  mgr.IncrementSdfPulseLimit("A", "Z", -5, true, 2);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.reject_limit[0], 0u);
  EXPECT_EQ(pd.error_limit[0], 5u);
}

}  // namespace
