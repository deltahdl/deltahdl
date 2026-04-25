#include <gtest/gtest.h>

#include <string>

#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// =============================================================================
// §32.6 — Multiple SDF files
// =============================================================================

// §32.6 sentence 1: "More than one SDF file can be annotated." Two
// successive ABSOLUTE annotations to the same path under the second
// $sdf_annotate call must overwrite the first call's installed delays —
// the ordered-process rule of §32.5 extends across files. With the
// second call's payload also written via ABSOLUTE, the matched
// PathDelay's delays must reflect only the second file's values.
TEST(SdfMultipleFiles, SecondAbsoluteFileOverwritesFirstFilesPathDelay) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;
  pre.delays[0] = 1;
  mgr.AddPathDelay(pre);

  SdfFile first;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH A Z (10) (20))))))
  )", first));
  AnnotateSdfToManager(first, mgr, SdfMtm::kTypical);

  SdfFile second;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH A Z (50) (80))))))
  )", second));
  AnnotateSdfToManager(second, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.delays[0], 50u);
  EXPECT_EQ(pd.delays[1], 80u);
}

// §32.6 sentence 1 companion: a second SDF file that names a different
// path must leave the first file's annotation intact. Without this,
// "more than one SDF file can be annotated" would be defeated by the
// second call wiping unrelated state. Pairs with the overwrite test
// above so an implementation that resets the manager on every call
// fails this one.
TEST(SdfMultipleFiles, SecondFilePreservesUntouchedAnnotationsFromFirst) {
  SpecifyManager mgr;
  PathDelay a;
  a.src_port = "A";
  a.dst_port = "Z";
  a.delay_count = 1;
  a.delays[0] = 1;
  mgr.AddPathDelay(a);
  PathDelay b;
  b.src_port = "B";
  b.dst_port = "Y";
  b.delay_count = 1;
  b.delays[0] = 1;
  mgr.AddPathDelay(b);

  SdfFile first;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH A Z (10) (20))))))
  )", first));
  AnnotateSdfToManager(first, mgr, SdfMtm::kTypical);

  SdfFile second;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH B Y (40) (60))))))
  )", second));
  AnnotateSdfToManager(second, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 2u);
  bool saw_first = false;
  bool saw_second = false;
  for (const auto& pd : mgr.GetPathDelays()) {
    if (pd.src_port == "A" && pd.dst_port == "Z") {
      EXPECT_EQ(pd.delays[0], 10u);
      EXPECT_EQ(pd.delays[1], 20u);
      saw_first = true;
    } else if (pd.src_port == "B" && pd.dst_port == "Y") {
      EXPECT_EQ(pd.delays[0], 40u);
      EXPECT_EQ(pd.delays[1], 60u);
      saw_second = true;
    }
  }
  EXPECT_TRUE(saw_first);
  EXPECT_TRUE(saw_second);
}

// §32.6 sentence 3: "Annotated values either modify (INCREMENT) or
// overwrite (ABSOLUTE) values from earlier SDF files." With the first
// call installing IOPATH A Z = (10, 20) under ABSOLUTE and the second
// call carrying IOPATH A Z = (5, 3) under INCREMENT, the post-second
// PathDelay must hold the per-direction sum (15, 23) — the modify
// rule additively combines the new INCREMENT values with the values
// the first file installed.
TEST(SdfMultipleFiles, IncrementFromSecondFileAddsToFirstFilesPathDelay) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;
  pre.delays[0] = 1;
  mgr.AddPathDelay(pre);

  SdfFile first;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH A Z (10) (20))))))
  )", first));
  AnnotateSdfToManager(first, mgr, SdfMtm::kTypical);

  SdfFile second;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (INCREMENT (IOPATH A Z (5) (3))))))
  )", second));
  AnnotateSdfToManager(second, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.delays[0], 15u);
  EXPECT_EQ(pd.delays[1], 23u);
}

// §32.6 sentence 3, three-call interleave: ABSOLUTE → INCREMENT → ABSOLUTE.
// The trailing ABSOLUTE call must wipe the accumulated state and
// install only its own payload, exercising the "overwrite (ABSOLUTE)"
// half of the rule even after a modify (INCREMENT) has run. Without
// this, a buggy increment store could let the modified value leak past
// the trailing overwrite.
TEST(SdfMultipleFiles, AbsoluteAfterIncrementWipesAccumulatedValue) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;
  pre.delays[0] = 1;
  mgr.AddPathDelay(pre);

  SdfFile first;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH A Z (10) (20))))))
  )", first));
  AnnotateSdfToManager(first, mgr, SdfMtm::kTypical);

  SdfFile second;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (INCREMENT (IOPATH A Z (5) (3))))))
  )", second));
  AnnotateSdfToManager(second, mgr, SdfMtm::kTypical);

  SdfFile third;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH A Z (50) (80))))))
  )", third));
  AnnotateSdfToManager(third, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.delays[0], 50u);
  EXPECT_EQ(pd.delays[1], 80u);
}

// §32.6 sentence 3 on the interconnect category: the second file's
// ABSOLUTE INTERCONNECT entry must overwrite the first file's same
// (src, dst) entry. Mirrors the path-delay overwrite test on the
// interconnect store so a category-specific bug cannot pass the
// path-delay tests while leaking through the interconnect store.
TEST(SdfMultipleFiles,
     SecondAbsoluteFileOverwritesFirstFilesInterconnectDelay) {
  SpecifyManager mgr;

  SdfFile first;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "net")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (INTERCONNECT s d (5))))))
  )", first));
  AnnotateSdfToManager(first, mgr, SdfMtm::kTypical);

  SdfFile second;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "net")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (INTERCONNECT s d (8))))))
  )", second));
  AnnotateSdfToManager(second, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetInterconnectDelays().size(), 1u);
  const auto& ic = mgr.GetInterconnectDelays()[0];
  EXPECT_EQ(ic.src_port, "s");
  EXPECT_EQ(ic.dst_port, "d");
  EXPECT_EQ(ic.rise, 8u);
}

// §32.6 sentence 3 on the interconnect category, modify side: a second
// file's INCREMENT INTERCONNECT entry must add to the first file's
// rise/fall payload rather than overwrite it. Together with the
// ABSOLUTE-overwrite test above, this proves both halves of the
// modify/overwrite rule on a non-path-delay category.
TEST(SdfMultipleFiles,
     IncrementFromSecondFileAddsToFirstFilesInterconnectDelay) {
  SpecifyManager mgr;

  SdfFile first;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "net")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (INTERCONNECT s d (5) (7))))))
  )", first));
  AnnotateSdfToManager(first, mgr, SdfMtm::kTypical);

  SdfFile second;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "net")
        (INSTANCE u1)
        (DELAY (INCREMENT (INTERCONNECT s d (2) (3))))))
  )", second));
  AnnotateSdfToManager(second, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetInterconnectDelays().size(), 1u);
  const auto& ic = mgr.GetInterconnectDelays()[0];
  EXPECT_EQ(ic.src_port, "s");
  EXPECT_EQ(ic.dst_port, "d");
  EXPECT_EQ(ic.rise, 7u);
  EXPECT_EQ(ic.fall, 10u);
}

// §32.6 sentence 4: "Different regions of a design can be annotated
// from different SDF files by specifying the region's hierarchy scope
// as the second argument to $sdf_annotate." When the caller passes a
// non-empty scope, only cells whose INSTANCE sits at or under that
// scope must be annotated; cells outside the scope must be skipped
// entirely. Two cells in one file with disjoint hierarchies, scoped to
// just one of them, exercises the filter — only the in-scope cell's
// IOPATH lands on the manager.
TEST(SdfMultipleFiles, ScopeFilterSkipsCellsOutsideHierarchyScope) {
  SpecifyManager mgr;

  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1/dut)
        (DELAY (ABSOLUTE (IOPATH A Z (10) (20)))))
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u2/dut)
        (DELAY (ABSOLUTE (IOPATH B Y (40) (60))))))
  )", file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical, "u1");

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.src_port, "A");
  EXPECT_EQ(pd.dst_port, "Z");
  EXPECT_EQ(pd.delays[0], 10u);
  EXPECT_EQ(pd.delays[1], 20u);
}

// §32.6 sentence 4 prefix-match: a scope is a hierarchy prefix, so a
// cell whose INSTANCE is hierarchically deeper than the scope (an
// SDF cell at u1/sub/dut under scope u1) sits inside the named
// region and must be annotated. The complementary skip test above
// pins down the negative side; this one pins down the positive side
// so a too-strict equality match cannot pass both.
TEST(SdfMultipleFiles,
     ScopeFilterAnnotatesCellsHierarchicallyUnderTheScope) {
  SpecifyManager mgr;

  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1/sub/dut)
        (DELAY (ABSOLUTE (IOPATH A Z (10) (20))))))
  )", file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical, "u1");

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.delays[0], 10u);
  EXPECT_EQ(pd.delays[1], 20u);
}

// §32.6 sentence 4 exact-match: the scope is a region, and a cell
// whose INSTANCE equals the scope (no deeper hierarchy under it) is
// the boundary case of "at or under that scope". This exercises the
// equality leg of the prefix matcher so that an implementation that
// requires a trailing `/` to match cannot accept it.
TEST(SdfMultipleFiles, ScopeFilterAnnotatesCellWhenInstanceEqualsScope) {
  SpecifyManager mgr;

  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH A Z (10) (20))))))
  )", file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical, "u1");

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.delays[0], 10u);
  EXPECT_EQ(pd.delays[1], 20u);
}

// §32.6 sentence 4 default scope: when the caller does not supply a
// scope, every cell in the file must be annotated regardless of
// instance — the filter must not silently exclude cells when no
// region was named. Without this, a regression that always applied
// the filter would drop annotations for callers that never passed a
// scope at all.
TEST(SdfMultipleFiles, EmptyScopeAnnotatesEveryCell) {
  SpecifyManager mgr;

  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1/dut)
        (DELAY (ABSOLUTE (IOPATH A Z (10) (20)))))
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u2/dut)
        (DELAY (ABSOLUTE (IOPATH B Y (40) (60))))))
  )", file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 2u);
}

// §32.6 sentence 4 prefix robustness: a scope of "u1" must not match
// a sibling cell whose INSTANCE happens to share that string as a
// non-hierarchical prefix (e.g., "u10/dut"). Without the trailing-
// separator requirement on the prefix match, a substring-style filter
// would silently annotate unrelated regions whose instance names share
// a leading substring with the named scope.
TEST(SdfMultipleFiles, ScopeFilterDoesNotMatchSiblingsWithSharedPrefix) {
  SpecifyManager mgr;

  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u10/dut)
        (DELAY (ABSOLUTE (IOPATH A Z (10) (20))))))
  )", file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical, "u1");

  EXPECT_EQ(mgr.GetPathDelays().size(), 0u);
}

// §32.6 combination: two files plus per-file scopes — the canonical
// "different regions ... from different SDF files" pattern. File A
// scoped to u1 installs the u1 cell's IOPATH; file B scoped to u2
// installs the u2 cell's IOPATH; both annotations coexist on the
// manager and neither file's scope filter spills onto the other
// region. Pins down that the two new behaviors of §32.6 — multi-file
// accumulation and per-call scoping — compose without interference.
TEST(SdfMultipleFiles,
     TwoCallsWithDifferentScopesAnnotateDifferentRegions) {
  SpecifyManager mgr;

  SdfFile file_a;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1/dut)
        (DELAY (ABSOLUTE (IOPATH A Z (10) (20)))))
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u2/dut)
        (DELAY (ABSOLUTE (IOPATH B Y (40) (60))))))
  )", file_a));
  AnnotateSdfToManager(file_a, mgr, SdfMtm::kTypical, "u1");

  SdfFile file_b;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1/dut)
        (DELAY (ABSOLUTE (IOPATH A Z (99) (99)))))
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u2/dut)
        (DELAY (ABSOLUTE (IOPATH B Y (40) (60))))))
  )", file_b));
  AnnotateSdfToManager(file_b, mgr, SdfMtm::kTypical, "u2");

  ASSERT_EQ(mgr.GetPathDelays().size(), 2u);
  bool saw_a = false;
  bool saw_b = false;
  for (const auto& pd : mgr.GetPathDelays()) {
    if (pd.src_port == "A" && pd.dst_port == "Z") {
      EXPECT_EQ(pd.delays[0], 10u);
      EXPECT_EQ(pd.delays[1], 20u);
      saw_a = true;
    } else if (pd.src_port == "B" && pd.dst_port == "Y") {
      EXPECT_EQ(pd.delays[0], 40u);
      EXPECT_EQ(pd.delays[1], 60u);
      saw_b = true;
    }
  }
  EXPECT_TRUE(saw_a);
  EXPECT_TRUE(saw_b);
}

// §32.6 sentence 3 on the specparam category: a second SDF file that
// rewrites a specparam already named by a first file must leave the
// later value behind, exercising the ABSOLUTE half of the cross-file
// modify/overwrite rule on the third backannotation category. Mirrors
// the path-delay and interconnect overwrite tests above so a category-
// specific bug cannot pass the other two while leaking a stale specparam
// through. (Originally lived in `test_simulator_clause_32_04.cpp` framed
// as a §32.4-sentence-5 replacement test, but the cross-file aspect is
// what §32.6 sentence 3 names — §32.4's "replacing" rule is single-file.)
TEST(SdfMultipleFiles,
     SecondAbsoluteFileOverwritesFirstFilesSpecparamValue) {
  SpecifyManager mgr;

  SdfFile first;
  {
    SdfCell cell;
    SdfSpecparam sp;
    sp.name = "tHold";
    sp.value.typ_val = 11;
    cell.specparams.push_back(sp);
    first.cells.push_back(cell);
  }
  AnnotateSdfToManager(first, mgr, SdfMtm::kTypical);

  SdfFile second;
  {
    SdfCell cell;
    SdfSpecparam sp;
    sp.name = "tHold";
    sp.value.typ_val = 47;
    cell.specparams.push_back(sp);
    second.cells.push_back(cell);
  }
  AnnotateSdfToManager(second, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetSpecparamValues().size(), 1u);
  EXPECT_EQ(mgr.GetSpecparamValues()[0].value, 47u);
}

// §32.6 sentence 3 on a conditional path: the cross-file ABSOLUTE
// overwrite rule applies regardless of whether the matched specify
// path is conditional. With a SystemVerilog `if (mode)` path declared
// up-front and two SDF files each carrying a COND IOPATH that names
// the same condition, the second file's payload (33/44) must replace
// the first file's (11/22) on the matched conditional sibling. The
// non-conditional companion `SecondAbsoluteFileOverwritesFirstFiles
// PathDelay` already pins the cross-file rule on bare paths; this
// test covers the conditional shape so a regression in the
// identity-tuple matching that AddPathDelay performs for conditional
// entries cannot let a stale value survive a second annotation pass.
// (Originally lived in `test_simulator_clause_32_04_01.cpp` framed
// as a §32.4.1 + §32.4-sentence-5 reannotation test, but the unique
// observation — second value wins — is what §32.6 sentence 3 names.
// §32.4.1's standalone conditional matching is already covered by
// `ConditionalIopathAnnotatesOnlyMatchingConditionPath`.)
TEST(SdfMultipleFiles,
     SecondAbsoluteFileOverwritesFirstFilesConditionalPathDelay) {
  SpecifyManager mgr;
  PathDelay sv;
  sv.src_port = "a";
  sv.dst_port = "y";
  sv.condition = "mode";
  sv.delay_count = 1;
  sv.delays[0] = 0;
  mgr.AddPathDelay(sv);

  SdfFile first;
  {
    SdfCell cell;
    SdfIopath io;
    io.src_port = "a";
    io.dst_port = "y";
    io.condition = "mode";
    io.rise.typ_val = 11;
    io.fall.typ_val = 22;
    cell.iopaths.push_back(io);
    first.cells.push_back(cell);
  }
  AnnotateSdfToManager(first, mgr, SdfMtm::kTypical);

  SdfFile second;
  {
    SdfCell cell;
    SdfIopath io;
    io.src_port = "a";
    io.dst_port = "y";
    io.condition = "mode";
    io.rise.typ_val = 33;
    io.fall.typ_val = 44;
    cell.iopaths.push_back(io);
    second.cells.push_back(cell);
  }
  AnnotateSdfToManager(second, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  EXPECT_EQ(mgr.GetPathDelays()[0].condition, "mode");
  EXPECT_EQ(mgr.GetPathDelays()[0].delays[0], 33u);
  EXPECT_EQ(mgr.GetPathDelays()[0].delays[1], 44u);
}

// §32.6 sentence 3 INCREMENT chain: each subsequent INCREMENT modifies
// "values from earlier SDF files" — including values that earlier INCREMENT
// passes themselves installed. Two INCREMENT calls following an ABSOLUTE
// must therefore accumulate: the second INCREMENT adds onto the running
// total, not onto the original ABSOLUTE baseline. Without cumulative
// INCREMENT semantics, a buggy implementation that always added onto the
// most recent ABSOLUTE would pass the single-INCREMENT test but lose the
// middle file's contribution here.
TEST(SdfMultipleFiles, ChainedIncrementCallsAccumulateOntoPathDelay) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;
  pre.delays[0] = 1;
  mgr.AddPathDelay(pre);

  SdfFile first;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH A Z (10) (20))))))
  )", first));
  AnnotateSdfToManager(first, mgr, SdfMtm::kTypical);

  SdfFile second;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (INCREMENT (IOPATH A Z (3) (5))))))
  )", second));
  AnnotateSdfToManager(second, mgr, SdfMtm::kTypical);

  SdfFile third;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (INCREMENT (IOPATH A Z (4) (7))))))
  )", third));
  AnnotateSdfToManager(third, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  // 10 + 3 + 4 = 17, 20 + 5 + 7 = 32 — second INC must build on first INC's
  // running total, not reset to the original ABSOLUTE.
  EXPECT_EQ(pd.delays[0], 17u);
  EXPECT_EQ(pd.delays[1], 32u);
}

// §32.6 sentence 4 on the interconnect category: the scope filter must
// be applied at the cell level, so an INTERCONNECT entry in an out-of-
// scope cell is skipped just like an IOPATH would be. Without this, a
// regression that only honoured scope on the IOPATH branch would let
// stray interconnect delays leak through. Two cells with disjoint
// hierarchies, scoped to one of them, isolate the rule for the
// interconnect store.
TEST(SdfMultipleFiles, ScopeFilterAlsoSkipsInterconnectsFromOutOfScopeCells) {
  SpecifyManager mgr;

  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "net")
        (INSTANCE u1/dut)
        (DELAY (ABSOLUTE (INTERCONNECT s1 d1 (5)))))
      (CELL
        (CELLTYPE "net")
        (INSTANCE u2/dut)
        (DELAY (ABSOLUTE (INTERCONNECT s2 d2 (8))))))
  )", file));
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical, "u1");

  ASSERT_EQ(mgr.GetInterconnectDelays().size(), 1u);
  const auto& ic = mgr.GetInterconnectDelays()[0];
  EXPECT_EQ(ic.src_port, "s1");
  EXPECT_EQ(ic.dst_port, "d1");
  EXPECT_EQ(ic.rise, 5u);
}

// §32.6 sentence 4 on the specparam category: the same cell-level scope
// filter must drop specparam updates from out-of-scope cells. Mirrors
// the interconnect coverage above so a regression that only honoured
// scope on path-delay categories cannot pass the IOPATH and INTERCONNECT
// tests while letting specparam writes from another region escape. A
// programmatic SdfFile is used because the LABEL section's specparam
// grammar is the same shape regardless of source.
TEST(SdfMultipleFiles, ScopeFilterAlsoSkipsSpecparamsFromOutOfScopeCells) {
  SpecifyManager mgr;

  SdfFile file;
  {
    SdfCell cell;
    cell.instance = "u1/dut";
    SdfSpecparam sp;
    sp.name = "tHoldKept";
    sp.value.typ_val = 11;
    cell.specparams.push_back(sp);
    file.cells.push_back(cell);
  }
  {
    SdfCell cell;
    cell.instance = "u2/dut";
    SdfSpecparam sp;
    sp.name = "tHoldDropped";
    sp.value.typ_val = 99;
    cell.specparams.push_back(sp);
    file.cells.push_back(cell);
  }
  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical, "u1");

  ASSERT_EQ(mgr.GetSpecparamValues().size(), 1u);
  EXPECT_EQ(mgr.GetSpecparamValues()[0].name, "tHoldKept");
  EXPECT_EQ(mgr.GetSpecparamValues()[0].value, 11u);
}

// §32.6 sentence 3 INCREMENT on the specparam category: when a later
// SDF file's LABEL section uses INCREMENT, the new value adds onto the
// specparam's existing total instead of overwriting it. The first
// ABSOLUTE call seeds the specparam at 11; the second INCREMENT call
// supplies 7; the post-second total must be 18. Without specparam-side
// INCREMENT support, the parser used to record the LABEL entry as
// unannotatable and the value would silently stay at 11 — this test
// pins down that §32.6's modify-mode now reaches all three categories
// (path delays, interconnects, specparams) uniformly.
TEST(SdfMultipleFiles,
     IncrementFromSecondFileAddsToFirstFilesSpecparamValue) {
  SpecifyManager mgr;

  SdfFile first;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (LABEL (ABSOLUTE (tHold 11)))))
  )", first));
  AnnotateSdfToManager(first, mgr, SdfMtm::kTypical);

  SdfFile second;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (LABEL (INCREMENT (tHold 7)))))
  )", second));
  AnnotateSdfToManager(second, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetSpecparamValues().size(), 1u);
  EXPECT_EQ(mgr.GetSpecparamValues()[0].name, "tHold");
  EXPECT_EQ(mgr.GetSpecparamValues()[0].value, 18u);
}

}  // namespace
