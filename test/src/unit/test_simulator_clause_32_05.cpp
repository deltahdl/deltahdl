#include <gtest/gtest.h>

#include <string>

#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

TEST(SdfMultipleAnnotations, IopathAfterPathpulseOverwritesPulseLimits) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;
  pre.delays[0] = 1;
  mgr.AddPathDelay(pre);

  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE
          (PATHPULSE A Z (10) (20))
          (IOPATH A Z (35) (61))))))
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.delays[0], 35u);
  EXPECT_EQ(pd.delays[1], 61u);

  EXPECT_EQ(pd.reject_limit[0], 35u);
  EXPECT_EQ(pd.error_limit[0], 35u);
  EXPECT_EQ(pd.reject_limit[1], 61u);
  EXPECT_EQ(pd.error_limit[1], 61u);
}

TEST(SdfMultipleAnnotations, PathpulseAfterIopathSetsPulseLimits) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;
  pre.delays[0] = 1;
  mgr.AddPathDelay(pre);

  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE
          (IOPATH A Z (35) (61))
          (PATHPULSE A Z (10) (20))))))
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.delays[0], 35u);
  EXPECT_EQ(pd.delays[1], 61u);
  EXPECT_EQ(pd.reject_limit[0], 10u);
  EXPECT_EQ(pd.error_limit[0], 20u);
}

TEST(SdfMultipleAnnotations,
     SimpleIopathAnnotationDefaultResetsPulseLimitsToDelays) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;
  pre.delays[0] = 1;

  pre.reject_limit[0] = 7;
  pre.error_limit[0] = 9;
  mgr.AddPathDelay(pre);

  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH A Z (50) (80))))))
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.delays[0], 50u);
  EXPECT_EQ(pd.delays[1], 80u);
  EXPECT_EQ(pd.reject_limit[0], 50u);
  EXPECT_EQ(pd.error_limit[0], 50u);
  EXPECT_EQ(pd.reject_limit[1], 80u);
  EXPECT_EQ(pd.error_limit[1], 80u);
}

TEST(SdfMultipleAnnotations,
     PortFollowedByInterconnectKeepsPortBaselineAndAddsSourceOverride) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "net")
        (INSTANCE u1)
        (DELAY (ABSOLUTE
          (PORT i15/in (6))
          (INTERCONNECT i13/out i15/in (5))))))
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  SpecifyManager mgr;
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetInterconnectDelays().size(), 2u);
  bool saw_port_baseline = false;
  bool saw_source_override = false;
  for (const auto& ic : mgr.GetInterconnectDelays()) {
    if (ic.src_port.empty() && ic.dst_port == "i15/in") {
      EXPECT_EQ(ic.rise, 6u);
      saw_port_baseline = true;
    } else if (ic.src_port == "i13/out" && ic.dst_port == "i15/in") {
      EXPECT_EQ(ic.rise, 5u);
      saw_source_override = true;
    }
  }
  EXPECT_TRUE(saw_port_baseline);
  EXPECT_TRUE(saw_source_override);
}

TEST(SdfMultipleAnnotations,
     InterconnectFollowedByPortOverwritesPriorInterconnectEntries) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "net")
        (INSTANCE u1)
        (DELAY (ABSOLUTE
          (INTERCONNECT i13/out i15/in (5))
          (PORT i15/in (6))))))
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  SpecifyManager mgr;
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetInterconnectDelays().size(), 1u);
  const auto& ic = mgr.GetInterconnectDelays()[0];
  EXPECT_TRUE(ic.src_port.empty());
  EXPECT_EQ(ic.dst_port, "i15/in");
  EXPECT_EQ(ic.rise, 6u);
}

TEST(SdfMultipleAnnotations,
     PortDoesNotOverwriteInterconnectsToOtherLoads) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "net")
        (INSTANCE u1)
        (DELAY (ABSOLUTE
          (INTERCONNECT i13/out i14/in (5))
          (PORT i15/in (6))))))
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  SpecifyManager mgr;
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetInterconnectDelays().size(), 2u);
  bool saw_other_load = false;
  bool saw_new_port = false;
  for (const auto& ic : mgr.GetInterconnectDelays()) {
    if (ic.src_port == "i13/out" && ic.dst_port == "i14/in") {
      EXPECT_EQ(ic.rise, 5u);
      saw_other_load = true;
    } else if (ic.src_port.empty() && ic.dst_port == "i15/in") {
      EXPECT_EQ(ic.rise, 6u);
      saw_new_port = true;
    }
  }
  EXPECT_TRUE(saw_other_load);
  EXPECT_TRUE(saw_new_port);
}

TEST(SdfMultipleAnnotations, MultiplePathpulsesBeforeIopathAreAllOverwritten) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;
  pre.delays[0] = 1;
  mgr.AddPathDelay(pre);

  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE
          (PATHPULSE A Z (10) (20))
          (PATHPULSE A Z (30) (40))
          (IOPATH A Z (35) (61))))))
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.delays[0], 35u);
  EXPECT_EQ(pd.delays[1], 61u);
  EXPECT_EQ(pd.reject_limit[0], 35u);
  EXPECT_EQ(pd.error_limit[0], 35u);
  EXPECT_EQ(pd.reject_limit[1], 61u);
  EXPECT_EQ(pd.error_limit[1], 61u);
}

TEST(SdfMultipleAnnotations,
     PathpulseInterleavedBetweenIopathsObservesFinalAnnotation) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;
  pre.delays[0] = 1;
  mgr.AddPathDelay(pre);

  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE
          (PATHPULSE A Z (10) (20))
          (IOPATH A Z (35) (61))
          (PATHPULSE A Z (20) (30))))))
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.delays[0], 35u);
  EXPECT_EQ(pd.delays[1], 61u);

  EXPECT_EQ(pd.reject_limit[0], 20u);
  EXPECT_EQ(pd.error_limit[0], 30u);
}

TEST(SdfMultipleAnnotations, RepeatedIopathOnSamePathLeavesOnlyFinalDelays) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;
  pre.delays[0] = 1;
  mgr.AddPathDelay(pre);

  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE
          (IOPATH A Z (35) (61))
          (IOPATH A Z (50) (80))))))
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.delays[0], 50u);
  EXPECT_EQ(pd.delays[1], 80u);

  EXPECT_EQ(pd.reject_limit[0], 50u);
  EXPECT_EQ(pd.error_limit[0], 50u);
  EXPECT_EQ(pd.reject_limit[1], 80u);
  EXPECT_EQ(pd.error_limit[1], 80u);
}

TEST(SdfMultipleAnnotations,
     PortInterconnectPortSequenceLeavesOnlyFinalPort) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "net")
        (INSTANCE u1)
        (DELAY (ABSOLUTE
          (PORT i15/in (3))
          (INTERCONNECT i13/out i15/in (5))
          (PORT i15/in (9))))))
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  SpecifyManager mgr;
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetInterconnectDelays().size(), 1u);
  const auto& ic = mgr.GetInterconnectDelays()[0];
  EXPECT_TRUE(ic.src_port.empty());
  EXPECT_EQ(ic.dst_port, "i15/in");
  EXPECT_EQ(ic.rise, 9u);
}

TEST(SdfMultipleAnnotations,
     RepeatedInterconnectSameSrcDstReplacesPriorPayload) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "net")
        (INSTANCE u1)
        (DELAY (ABSOLUTE
          (INTERCONNECT i13/out i15/in (5))
          (INTERCONNECT i13/out i15/in (8))))))
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  SpecifyManager mgr;
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetInterconnectDelays().size(), 1u);
  const auto& ic = mgr.GetInterconnectDelays()[0];
  EXPECT_EQ(ic.src_port, "i13/out");
  EXPECT_EQ(ic.dst_port, "i15/in");
  EXPECT_EQ(ic.rise, 8u);
}

TEST(SdfMultipleAnnotations,
     PortFollowedByNetdelaySameLoadOverwritesPriorPort) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "net")
        (INSTANCE u1)
        (DELAY (ABSOLUTE
          (PORT i15/in (4))
          (NETDELAY i15/in (7))))))
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  SpecifyManager mgr;
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetInterconnectDelays().size(), 1u);
  const auto& ic = mgr.GetInterconnectDelays()[0];
  EXPECT_TRUE(ic.src_port.empty());
  EXPECT_EQ(ic.dst_port, "i15/in");
  EXPECT_EQ(ic.rise, 7u);
}

TEST(SdfMultipleAnnotations,
     ExtendedIopathWithEmptyPulseSlotsPreservesPriorPathpulse) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;

  pre.delays[0] = 20;
  mgr.AddPathDelay(pre);

  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE
          (PATHPULSE A Z (10) (20))
          (IOPATH A Z ((35) () ()) ((61) () ()))))))
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.delays[0], 35u);
  EXPECT_EQ(pd.delays[1], 61u);

  EXPECT_EQ(pd.reject_limit[0], 10u);
  EXPECT_EQ(pd.error_limit[0], 20u);
}

TEST(SdfMultipleAnnotations,
     ParserMarksExtendedIopathWithEmptyPulseSlotsAsAbsent) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH A Z ((35) () ()) ((61) () ()))))))
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  ASSERT_EQ(file.cells[0].iopaths.size(), 1u);
  const auto& io = file.cells[0].iopaths[0];
  EXPECT_TRUE(io.extended_form);
  EXPECT_TRUE(io.rise_delay_present);
  EXPECT_TRUE(io.fall_delay_present);
  EXPECT_FALSE(io.rise_reject_present);
  EXPECT_FALSE(io.rise_error_present);
  EXPECT_FALSE(io.fall_reject_present);
  EXPECT_FALSE(io.fall_error_present);
  EXPECT_EQ(io.rise.typ_val, 35u);
  EXPECT_EQ(io.fall.typ_val, 61u);
}

TEST(SdfMultipleAnnotations,
     ExtendedIopathWithSuppliedPulseSlotsInstallsAsCombinedAnnotation) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;
  pre.delays[0] = 1;
  mgr.AddPathDelay(pre);

  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE
          (IOPATH A Z ((35) (4) (7)) ((61) (4) (7)))))))
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.delays[0], 35u);
  EXPECT_EQ(pd.delays[1], 61u);
  EXPECT_EQ(pd.reject_limit[0], 4u);
  EXPECT_EQ(pd.error_limit[0], 7u);
  EXPECT_EQ(pd.reject_limit[1], 4u);
  EXPECT_EQ(pd.error_limit[1], 7u);
}

TEST(SdfMultipleAnnotations,
     ExtendedCombinedIopathMatchesSeparatePathpulseThenIopath) {
  auto seed = []() {
    SpecifyManager m;
    PathDelay pd;
    pd.src_port = "A";
    pd.dst_port = "Z";
    pd.delay_count = 1;

    for (int i = 0; i < 12; ++i) pd.delays[i] = 10;
    m.AddPathDelay(pd);
    return m;
  };

  SpecifyManager mgr_separate = seed();
  SdfFile file_separate;
  std::string sdf_separate = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE
          (PATHPULSE A Z (4) (7))
          (IOPATH A Z ((35) () ()) ((61) () ()))))))
  )";
  ASSERT_TRUE(ParseSdf(sdf_separate, file_separate));
  AnnotateSdfToManager(file_separate, mgr_separate, SdfMtm::kTypical);

  SpecifyManager mgr_combined = seed();
  SdfFile file_combined;
  std::string sdf_combined = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE
          (IOPATH A Z ((35) (4) (7)) ((61) (4) (7)))))))
  )";
  ASSERT_TRUE(ParseSdf(sdf_combined, file_combined));
  AnnotateSdfToManager(file_combined, mgr_combined, SdfMtm::kTypical);

  ASSERT_EQ(mgr_separate.GetPathDelays().size(), 1u);
  ASSERT_EQ(mgr_combined.GetPathDelays().size(), 1u);
  const auto& pd_separate = mgr_separate.GetPathDelays()[0];
  const auto& pd_combined = mgr_combined.GetPathDelays()[0];
  EXPECT_EQ(pd_combined.delays[0], pd_separate.delays[0]);
  EXPECT_EQ(pd_combined.delays[1], pd_separate.delays[1]);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd_combined.reject_limit[i], pd_separate.reject_limit[i])
        << "reject_limit mismatch at slot " << i;
    EXPECT_EQ(pd_combined.error_limit[i], pd_separate.error_limit[i])
        << "error_limit mismatch at slot " << i;
  }
}

}
