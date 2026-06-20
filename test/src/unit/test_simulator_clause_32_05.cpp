#include <gtest/gtest.h>

#include <string>

#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// Seeds a SpecifyManager with a single A->Z PathDelay whose first delay slot is
// set to |delay0|. Shared by the §32.5 ordered-process tests that need a prior
// annotation in place before applying an SDF overwrite.
SpecifyManager SeedManagerWithPathDelay(unsigned delay0) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;
  pre.delays[0] = delay0;
  mgr.AddPathDelay(pre);
  return mgr;
}

// §32.5 C1 (ordered process): a later construct overwrites an earlier one even
// when the two are different constructs. PATHPULSE seeds pulse limits, then a
// plain IOPATH resets them to the delay-derived defaults.
TEST(SdfMultipleAnnotations, IopathAfterPathpulseOverwritesPulseLimits) {
  SpecifyManager mgr = SeedManagerWithPathDelay(1);

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

// §32.5 C1 order sensitivity: the same two constructs in the opposite order
// yield the opposite outcome. With PATHPULSE last, its pulse limits survive.
TEST(SdfMultipleAnnotations, PathpulseAfterIopathSetsPulseLimits) {
  SpecifyManager mgr = SeedManagerWithPathDelay(1);

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

// §32.5 S1: a PORT annotation followed by an INTERCONNECT annotation to the
// same load affects only the interconnect source; the PORT baseline (modeled
// as an all-sources entry with empty src) persists for every other source.
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

// §32.5 S2: an INTERCONNECT annotation followed by a PORT annotation to the
// same load overwrites the interconnect; the load takes the PORT delay from
// all sources. This is the order-swapped counterpart of the S1 test above.
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

// §32.5 S2 "same load" scoping: the overwriting PORT touches only its own load,
// leaving interconnect annotations to other loads intact.
TEST(SdfMultipleAnnotations, PortDoesNotOverwriteInterconnectsToOtherLoads) {
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

// §32.5 C1 for a repeated same construct: a subsequent INTERCONNECT to the same
// source/load pair replaces the prior payload (last occurrence wins).
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

// §32.5: overwriting can be avoided with empty parentheses that hold the
// current pulse-limit values. The IOPATH supplies only delays, so the prior
// PATHPULSE limits are preserved rather than reset.
TEST(SdfMultipleAnnotations,
     ExtendedIopathWithEmptyPulseSlotsPreservesPriorPathpulse) {
  SpecifyManager mgr = SeedManagerWithPathDelay(20);

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

// §32.5: the separate PATHPULSE-then-IOPATH(empty-slots) form can be simplified
// into a single combined IOPATH statement; both must annotate identically.
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

// §32.5 C1 modify-half: a subsequent annotation can *modify* (INCREMENT) an
// earlier one rather than overwrite it. An ABSOLUTE IOPATH establishes the
// delay; a later INCREMENT IOPATH on the same path adds to it, so the running
// value is changed by accumulation, not replacement.
TEST(SdfMultipleAnnotations, IncrementIopathModifiesPriorAbsoluteAnnotation) {
  SdfFile file;
  std::string sdf = R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH A Z (35) (61))))
        (DELAY (INCREMENT (IOPATH A Z (5) (5))))))
  )";
  ASSERT_TRUE(ParseSdf(sdf, file));
  SpecifyManager mgr;
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.delays[0], 40u);
  EXPECT_EQ(pd.delays[1], 66u);
}

}  // namespace
