#include <gtest/gtest.h>

#include <string>

#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// =============================================================================
// §32.5 — Multiple annotations
// =============================================================================

// §32.5 sentence 1: "SDF annotation is an ordered process. The constructs
// from the SDF file are annotated in their order of occurrence." With a
// PATHPULSE listed before an IOPATH on the same path inside a single
// ABSOLUTE block, the IOPATH must take effect last. The page-929 example
// pins down what "last" means: the IOPATH overwrites the pulse limits
// the prior PATHPULSE just installed, default-resetting reject and error
// to mirror the new propagation delays.
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
  // The IOPATH appears after the PATHPULSE in source order, so its
  // default-reset rule wipes the 10 / 20 pulse limits and reinstalls
  // the per-direction propagation delay as both reject and error.
  EXPECT_EQ(pd.reject_limit[0], 35u);
  EXPECT_EQ(pd.error_limit[0], 35u);
  EXPECT_EQ(pd.reject_limit[1], 61u);
  EXPECT_EQ(pd.error_limit[1], 61u);
}

// §32.5 sentence 1 (companion): swapping the order — IOPATH first, then
// PATHPULSE — must put the PATHPULSE last. The IOPATH supplies the new
// delays and the PATHPULSE overwrites the per-path pulse limits without
// disturbing the propagation delays. Pairs with the test above so an
// implementation that processes one category before another (rather
// than truly in source order) cannot pass both.
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

// §32.5 sentence 2: "annotation of an SDF construct can be changed by
// annotation of a subsequent construct that either modifies (INCREMENT)
// or overwrites (ABSOLUTE) it. These do not have to be the same
// construct." A bare IOPATH ABSOLUTE annotation must default-reset the
// path's pulse limits even when the prior limits were installed
// out-of-band — that is what makes the IOPATH "overwrite" a prior
// PATHPULSE. The cross-construct interaction is testable in isolation
// by seeding the path with non-default reject / error and confirming
// the IOPATH wipes them.
TEST(SdfMultipleAnnotations,
     SimpleIopathAnnotationDefaultResetsPulseLimitsToDelays) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;
  pre.delays[0] = 1;
  // Stand in for a prior PATHPULSE (or PATHPULSE$) that already pushed
  // the pulse limits away from the path-delay defaults. The §32.5
  // overwrite must win regardless of how those values got there.
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

// §32.5 example 4 ("PORT followed by INTERCONNECT"): "A PORT annotation
// followed by an INTERCONNECT annotation to the same load shall cause
// only the delay from the INTERCONNECT source to be affected." The PORT
// entry establishes the all-sources-to-load baseline (delay 6 in the
// LRM example); the subsequent INTERCONNECT names a specific source
// whose delay drops to 5 while the PORT baseline still answers for
// every other source.
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

// §32.5 example 5 ("INTERCONNECT followed by PORT"): "An INTERCONNECT
// annotation followed by a PORT annotation shall cause the INTERCONNECT
// annotation to be overwritten. Here, the delays from all sources to
// the load shall become 6." The PORT entry must wipe every prior
// source-specific INTERCONNECT entry whose load matches, leaving only
// the PORT baseline behind.
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

// §32.5 example 5, load-isolation edge: a PORT annotation only wipes
// entries whose load matches its own — INTERCONNECT entries to a
// different load survive. Without this carve-out an implementation
// could pass example 5 by clearing the entire interconnect store on
// every PORT, which would break unrelated nets.
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

// §32.5 sentence 1, robustness edge: a stretch of consecutive PATHPULSE
// annotations does not give any of them surviving status when an IOPATH
// then runs through the same path. The IOPATH's default-reset must wipe
// every prior PATHPULSE entry in the section, not just the most recent.
// An implementation that pulled PATHPULSE entries out of order — say,
// applied them all at the end — could pass the two-step example 1 test
// while still smuggling a stale value past a same-section IOPATH; this
// test forecloses that edge.
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

// §32.5 sentence 1, three-step interleave: PATHPULSE → IOPATH →
// PATHPULSE within one ABSOLUTE block exercises both directions of the
// cross-construct override at once. The middle IOPATH must wipe the
// first PATHPULSE's limits, and the trailing PATHPULSE must overwrite
// the IOPATH's default-reset limits without disturbing the propagation
// delays the IOPATH installed.
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
  // §32.7 last sentence: the trailing PATHPULSE values (20, 30) fit
  // within delays[0]=35, so neither component is clamped down to the
  // delay and both observable limits match the SDF text. Pins down
  // that the §32.5 source-order rule still distinguishes the trailing
  // PATHPULSE from the IOPATH default-reset (which would have left
  // both limits at 35).
  EXPECT_EQ(pd.reject_limit[0], 20u);
  EXPECT_EQ(pd.error_limit[0], 30u);
}

// §32.5 sentence 1, same-construct overwrite: the LRM phrases the rule
// in terms of "a subsequent construct" without restricting it to a
// different kind, so two IOPATHs on the same path within one ABSOLUTE
// block must leave only the second's payload behind. Pins down that
// same-construct repetition follows the same ordered-process rule as
// the cross-construct examples.
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
  // The second IOPATH's default-reset reinstalls reject/error from its
  // own delays, so the first IOPATH's reject/error must not leak through.
  EXPECT_EQ(pd.reject_limit[0], 50u);
  EXPECT_EQ(pd.error_limit[0], 50u);
  EXPECT_EQ(pd.reject_limit[1], 80u);
  EXPECT_EQ(pd.error_limit[1], 80u);
}

// §32.5 example 5, three-step interleave: PORT → INTERCONNECT → PORT
// to the same load. Both prior records (the original PORT baseline and
// the source-specific INTERCONNECT) must be wiped by the trailing PORT,
// leaving exactly one entry. Strengthens the two-step example 5 test by
// pinning that the wipe applies regardless of whether the prior records
// contain a PORT-shaped entry, an INTERCONNECT-shaped entry, or both.
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

// §32.5 sentence 1, same-key INTERCONNECT re-annotation: when two
// INTERCONNECT entries share the same source/destination pair within
// one ABSOLUTE block, the later one's delay payload replaces the
// earlier one. The store must not accumulate two records under the
// same (src, dst) tuple — that would let a stale delay survive into a
// later lookup.
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

// §32.5 sentence 2, "These do not have to be the same construct":
// PORT followed by NETDELAY to the same load is the load-only twin of
// example 5 — both constructs are load-only (empty source) by §32.4.4
// definition, so the trailing NETDELAY must wipe the prior PORT just
// as a trailing PORT would. Pins down that the load-only wipe rule
// applies symmetrically across PORT and NETDELAY rather than treating
// PORT specially.
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

// §32.5 example 2: an extended-form IOPATH whose reject and error slots
// are written as empty parens shall preserve the matched specify path's
// existing pulse limits while still installing the new propagation
// delays. The PATHPULSE that runs first establishes a non-default
// reject/error pair; the trailing IOPATH then overwrites the delays
// without disturbing those limits.
TEST(SdfMultipleAnnotations,
     ExtendedIopathWithEmptyPulseSlotsPreservesPriorPathpulse) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;
  // §32.7 last sentence: a baseline delay tall enough that the trailing
  // PATHPULSE values (10 / 20) sit at or below `delays[0]` and so are
  // not clamped. The preservation rule under test concerns the
  // empty-pulse-slot extended IOPATH, not the PATHPULSE clamp; seeding
  // a delay that admits the PATHPULSE values verbatim isolates the
  // preservation path.
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
  // Empty parens for reject and error keep the PATHPULSE-installed
  // limits; the IOPATH's default-reset is suppressed when no pulse-limit
  // slot was actually supplied.
  EXPECT_EQ(pd.reject_limit[0], 10u);
  EXPECT_EQ(pd.error_limit[0], 20u);
}

// §32.5 example 2, parser-level edge: the extended-form parser must not
// trip on the empty-parens slots — the parsed iopath's `extended_form`
// flag is set, every `*_present` reject/error flag for both directions
// is false, and the propagation delays on `rise` / `fall` come through
// unscathed. Without these signals reaching the annotator, the
// preservation rule above could not be observed.
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

// §32.5 example 3: the extended-form IOPATH `((d) (r) (e))` is the
// single-statement equivalent of a PATHPULSE followed by an IOPATH. The
// supplied reject and error must install onto every transition slot the
// matching path tracks, and the propagation delays must come from the
// outer triplet's first component just like the simple form.
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

// §32.5 example 3, equivalence claim: the extended-form combined IOPATH
// must produce the same reject_limit / error_limit on the matched path
// as a separate (PATHPULSE) (IOPATH) pair would. Run both forms against
// equally seeded managers and compare the resulting limits slot by
// slot — any divergence would mean the simplified form is not actually
// equivalent to the two-statement composition the LRM names.
TEST(SdfMultipleAnnotations,
     ExtendedCombinedIopathMatchesSeparatePathpulseThenIopath) {
  auto seed = []() {
    SpecifyManager m;
    PathDelay pd;
    pd.src_port = "A";
    pd.dst_port = "Z";
    pd.delay_count = 1;
    // §32.7 last sentence: every per-slot baseline delay sits at or
    // above the maximum PATHPULSE value (7), so neither the rise nor
    // the fall reject/error component is clamped on the separate-form
    // pass. With the clamp out of the picture, the §32.5 example-3
    // equivalence between the combined extended IOPATH and the
    // (PATHPULSE)+(IOPATH-with-empty-slots) pair holds slot by slot.
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

}  // namespace
