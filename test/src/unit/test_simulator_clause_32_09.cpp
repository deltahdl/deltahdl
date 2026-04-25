#include <gtest/gtest.h>

#include <cstdio>
#include <fstream>
#include <sstream>
#include <string>

#include "simulator/sdf_parser.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

TEST(SdfParser, ParseEmptyFile) {
  SdfFile file;
  bool ok = ParseSdf("(DELAYFILE)", file);
  EXPECT_TRUE(ok);
  EXPECT_TRUE(file.cells.empty());
}

TEST(SdfParser, ParseVersion) {
  SdfFile file;
  bool ok = ParseSdf(R"((DELAYFILE (SDFVERSION "4.0")))", file);
  EXPECT_TRUE(ok);
  EXPECT_EQ(file.version, "4.0");
}

TEST(SdfParser, ParseDesign) {
  SdfFile file;
  bool ok = ParseSdf(R"((DELAYFILE (DESIGN "top")))", file);
  EXPECT_TRUE(ok);
  EXPECT_EQ(file.design, "top");
}

// =============================================================================
// §32.9 — $sdf_annotate
// =============================================================================

// §32.9 Syntax 32-1: the system task records the (sdf_file,
// module_instance) pair so a later flush stage can apply the named
// SDF file under the chosen scope. With sdf_file = "timing.sdf" and
// module_instance = "top.dut", AnnotateSdf must keep both arguments
// addressable through GetSdfAnnotations() — the recording API is the
// only observable side-effect of $sdf_annotate at this stage, and a
// regression that dropped either argument would silently lose the
// $sdf_annotate request.
TEST(SdfAnnotateRequest, RecordsBothFileAndScopeArguments) {
  SpecifyManager mgr;
  mgr.AnnotateSdf({"timing.sdf", "top.dut"});
  ASSERT_EQ(mgr.GetSdfAnnotations().size(), 1u);
  EXPECT_EQ(mgr.GetSdfAnnotations()[0].sdf_file, "timing.sdf");
  EXPECT_EQ(mgr.GetSdfAnnotations()[0].scope, "top.dut");
}

// §32.9 Table 32-5: the four mtm_spec keywords ("MAXIMUM", "MINIMUM",
// "TYPICAL", "TOOL_CONTROL") shall map to their corresponding
// SdfMtmKeyword enumerator. A keyword string the LRM does not list
// must be rejected so callers can fall back to the LRM default
// instead of silently treating the unknown text as MTM-default.
TEST(SdfMtmKeyword, MaximumStringMapsToMaximumKeyword) {
  SdfMtmKeyword out = SdfMtmKeyword::kToolControl;
  EXPECT_TRUE(ParseSdfMtmKeyword("MAXIMUM", out));
  EXPECT_EQ(out, SdfMtmKeyword::kMaximum);
}

TEST(SdfMtmKeyword, MinimumStringMapsToMinimumKeyword) {
  SdfMtmKeyword out = SdfMtmKeyword::kToolControl;
  EXPECT_TRUE(ParseSdfMtmKeyword("MINIMUM", out));
  EXPECT_EQ(out, SdfMtmKeyword::kMinimum);
}

TEST(SdfMtmKeyword, TypicalStringMapsToTypicalKeyword) {
  SdfMtmKeyword out = SdfMtmKeyword::kToolControl;
  EXPECT_TRUE(ParseSdfMtmKeyword("TYPICAL", out));
  EXPECT_EQ(out, SdfMtmKeyword::kTypical);
}

TEST(SdfMtmKeyword, ToolControlStringMapsToToolControlKeyword) {
  SdfMtmKeyword out = SdfMtmKeyword::kMinimum;
  EXPECT_TRUE(ParseSdfMtmKeyword("TOOL_CONTROL", out));
  EXPECT_EQ(out, SdfMtmKeyword::kToolControl);
}

// §32.9 Table 32-5 + paragraph "TOOL_CONTROL (default)": when the
// caller does not pass an mtm_spec argument, ResolveSdfMtm with the
// TOOL_CONTROL keyword must hand back whatever MTM the simulator's
// own delay-mode setting names. Without this defaulting, every call
// site would silently fall back to typical regardless of the
// simulator setting and the LRM's "as selected by the simulator"
// rule would not be observable.
TEST(SdfMtmKeyword, ToolControlReturnsCallerSuppliedDefaultMtm) {
  EXPECT_EQ(ResolveSdfMtm(SdfMtmKeyword::kToolControl, SdfMtm::kMinimum),
            SdfMtm::kMinimum);
  EXPECT_EQ(ResolveSdfMtm(SdfMtmKeyword::kToolControl, SdfMtm::kTypical),
            SdfMtm::kTypical);
  EXPECT_EQ(ResolveSdfMtm(SdfMtmKeyword::kToolControl, SdfMtm::kMaximum),
            SdfMtm::kMaximum);
}

TEST(SdfMtmKeyword, NamedKeywordOverridesCallerSuppliedDefault) {
  // §32.9 Table 32-5: the three named keywords each select a fixed
  // slot regardless of the simulator's current preference, so passing
  // a different default through must not change the resolved MTM.
  EXPECT_EQ(ResolveSdfMtm(SdfMtmKeyword::kMaximum, SdfMtm::kMinimum),
            SdfMtm::kMaximum);
  EXPECT_EQ(ResolveSdfMtm(SdfMtmKeyword::kMinimum, SdfMtm::kMaximum),
            SdfMtm::kMinimum);
  EXPECT_EQ(ResolveSdfMtm(SdfMtmKeyword::kTypical, SdfMtm::kMaximum),
            SdfMtm::kTypical);
}

TEST(SdfMtmKeyword, UnknownStringIsRejectedAndLeavesOutputUntouched) {
  SdfMtmKeyword out = SdfMtmKeyword::kTypical;
  EXPECT_FALSE(ParseSdfMtmKeyword("BOGUS", out));
  EXPECT_EQ(out, SdfMtmKeyword::kTypical);
}

// §32.9 Table 32-6: the four scale_type keywords ("FROM_MTM",
// "FROM_MAXIMUM", "FROM_MINIMUM", "FROM_TYPICAL") shall map to their
// corresponding SdfScaleType enumerator. Pins down the 1:1
// correspondence the table requires.
TEST(SdfScaleTypeParser, FromMtmStringMapsToFromMtmKind) {
  SdfScaleType out = SdfScaleType::kFromMaximum;
  EXPECT_TRUE(ParseSdfScaleType("FROM_MTM", out));
  EXPECT_EQ(out, SdfScaleType::kFromMtm);
}

TEST(SdfScaleTypeParser, FromMaximumStringMapsToFromMaximumKind) {
  SdfScaleType out = SdfScaleType::kFromMtm;
  EXPECT_TRUE(ParseSdfScaleType("FROM_MAXIMUM", out));
  EXPECT_EQ(out, SdfScaleType::kFromMaximum);
}

TEST(SdfScaleTypeParser, FromMinimumStringMapsToFromMinimumKind) {
  SdfScaleType out = SdfScaleType::kFromMtm;
  EXPECT_TRUE(ParseSdfScaleType("FROM_MINIMUM", out));
  EXPECT_EQ(out, SdfScaleType::kFromMinimum);
}

TEST(SdfScaleTypeParser, FromTypicalStringMapsToFromTypicalKind) {
  SdfScaleType out = SdfScaleType::kFromMtm;
  EXPECT_TRUE(ParseSdfScaleType("FROM_TYPICAL", out));
  EXPECT_EQ(out, SdfScaleType::kFromTypical);
}

TEST(SdfScaleTypeParser, UnknownStringIsRejectedAndLeavesOutputUntouched) {
  SdfScaleType out = SdfScaleType::kFromTypical;
  EXPECT_FALSE(ParseSdfScaleType("FROM_NOWHERE", out));
  EXPECT_EQ(out, SdfScaleType::kFromTypical);
}

// §32.9 scale_factors paragraph: the default value is 1.0:1.0:1.0,
// so a fresh SdfScaleFactors must agree with that triplet.
// SdfScaleFactors is the storage that callers default to when no
// scale_factors argument is supplied; an inadvertent change to the
// defaults would silently shift every annotated value the moment a
// caller relied on the LRM-stated default.
TEST(SdfScaleFactors, DefaultMultipliersAreOnePointZero) {
  SdfScaleFactors sf;
  EXPECT_DOUBLE_EQ(sf.min_factor, 1.0);
  EXPECT_DOUBLE_EQ(sf.typ_factor, 1.0);
  EXPECT_DOUBLE_EQ(sf.max_factor, 1.0);
}

// §32.9 scale_factors paragraph example: the string "1.6:1.4:1.2"
// shall produce per-slot multipliers of 1.6 for min, 1.4 for typical,
// and 1.2 for maximum. Distinct values per slot are required so a
// mis-ordered triplet (e.g. swapping typ and max) is caught.
TEST(SdfScaleFactorsParser, ColonSeparatedTripletDecomposesIntoOrderedFactors) {
  SdfScaleFactors out;
  EXPECT_TRUE(ParseSdfScaleFactors("1.6:1.4:1.2", out));
  EXPECT_DOUBLE_EQ(out.min_factor, 1.6);
  EXPECT_DOUBLE_EQ(out.typ_factor, 1.4);
  EXPECT_DOUBLE_EQ(out.max_factor, 1.2);
}

TEST(SdfScaleFactorsParser, EmptyStringLeavesDefaultsInPlace) {
  SdfScaleFactors out;
  out.min_factor = 9.0;  // Sentinel — should be reset to 1.0 by parse.
  out.typ_factor = 9.0;
  out.max_factor = 9.0;
  EXPECT_TRUE(ParseSdfScaleFactors("", out));
  EXPECT_DOUBLE_EQ(out.min_factor, 1.0);
  EXPECT_DOUBLE_EQ(out.typ_factor, 1.0);
  EXPECT_DOUBLE_EQ(out.max_factor, 1.0);
}

// §32.9 Table 32-6 row "FROM_MTM (default)": each scale factor
// applies to its matching slot of the input triplet — min*sf_min,
// typ*sf_typ, max*sf_max — so the three slots scale independently.
// The LRM example "1.6:1.4:1.2" landed under the FROM_MTM default
// causes minimum values to be multiplied by 1.6, typical by 1.4 and
// maximum by 1.2, the wording §32.9 uses verbatim.
TEST(SdfScaling, FromMtmAppliesEachFactorToItsMatchingSlot) {
  SdfDelayValue v;
  v.min_val = 10;
  v.typ_val = 20;
  v.max_val = 30;
  SdfScaleFactors f;
  f.min_factor = 1.6;
  f.typ_factor = 1.4;
  f.max_factor = 1.2;
  auto out = ApplySdfScaling(v, SdfScaleType::kFromMtm, f);
  EXPECT_EQ(out.min_val, 16u);  // 10 * 1.6
  EXPECT_EQ(out.typ_val, 28u);  // 20 * 1.4
  EXPECT_EQ(out.max_val, 36u);  // 30 * 1.2
}

// §32.9 Table 32-6 row "FROM_MAXIMUM": every scaled output slot is
// derived from the input's maximum value, with each factor applied to
// that one source. Pins down the broadcast: a regression that read
// the matching slot instead of the max would still pass the
// FROM_MTM test above.
TEST(SdfScaling, FromMaximumDerivesEverySlotFromTheMaximumValue) {
  SdfDelayValue v;
  v.min_val = 10;
  v.typ_val = 20;
  v.max_val = 30;
  SdfScaleFactors f;
  f.min_factor = 1.6;
  f.typ_factor = 1.4;
  f.max_factor = 1.2;
  auto out = ApplySdfScaling(v, SdfScaleType::kFromMaximum, f);
  EXPECT_EQ(out.min_val, 48u);  // 30 * 1.6
  EXPECT_EQ(out.typ_val, 42u);  // 30 * 1.4
  EXPECT_EQ(out.max_val, 36u);  // 30 * 1.2
}

TEST(SdfScaling, FromMinimumDerivesEverySlotFromTheMinimumValue) {
  // §32.9 Table 32-6 row "FROM_MINIMUM": every scaled output slot is
  // derived from the input's minimum value. Companion to the
  // FROM_MAXIMUM test so the broadcast leg is observed on the
  // opposite end of the triplet.
  SdfDelayValue v;
  v.min_val = 10;
  v.typ_val = 20;
  v.max_val = 30;
  SdfScaleFactors f;
  f.min_factor = 1.6;
  f.typ_factor = 1.4;
  f.max_factor = 1.2;
  auto out = ApplySdfScaling(v, SdfScaleType::kFromMinimum, f);
  EXPECT_EQ(out.min_val, 16u);  // 10 * 1.6
  EXPECT_EQ(out.typ_val, 14u);  // 10 * 1.4
  EXPECT_EQ(out.max_val, 12u);  // 10 * 1.2
}

TEST(SdfScaling, FromTypicalDerivesEverySlotFromTheTypicalValue) {
  // §32.9 Table 32-6 row "FROM_TYPICAL": every scaled output slot is
  // derived from the input's typical value. Together with the
  // FROM_MAXIMUM and FROM_MINIMUM tests, exhausts the three
  // single-source rows of Table 32-6.
  SdfDelayValue v;
  v.min_val = 10;
  v.typ_val = 20;
  v.max_val = 30;
  SdfScaleFactors f;
  f.min_factor = 1.6;
  f.typ_factor = 1.4;
  f.max_factor = 1.2;
  auto out = ApplySdfScaling(v, SdfScaleType::kFromTypical, f);
  EXPECT_EQ(out.min_val, 32u);  // 20 * 1.6
  EXPECT_EQ(out.typ_val, 28u);  // 20 * 1.4
  EXPECT_EQ(out.max_val, 24u);  // 20 * 1.2
}

// §32.9 scale_factors default "1.0:1.0:1.0": when both arguments are
// at their LRM defaults (FROM_MTM scale_type, identity scale_factors),
// the scaled triplet must equal the input. Pins down the no-op default
// path so a regression that always rounds or always picks a single
// slot would be caught.
TEST(SdfScaling, DefaultScaleTypeAndIdentityFactorsPreserveInputTriplet) {
  SdfDelayValue v;
  v.min_val = 7;
  v.typ_val = 11;
  v.max_val = 13;
  SdfScaleFactors f;  // 1.0/1.0/1.0 by default.
  auto out = ApplySdfScaling(v, SdfScaleType::kFromMtm, f);
  EXPECT_EQ(out.min_val, 7u);
  EXPECT_EQ(out.typ_val, 11u);
  EXPECT_EQ(out.max_val, 13u);
}

// §32.9 scale_factors paragraph: when non-identity factors are piped
// through a real SDF annotation pass (parse → scale → annotate →
// MTM-select), the resulting installed delays must equal the per-slot
// scaled values picked by MTM. With the default FROM_MTM scale_type,
// an IOPATH supplying rise=10/fall=20 and factors 1.6:1.4:1.2 must
// land on the matched PathDelay as 14/28 under typical MTM (typ_val
// times the typical factor). Without integration coverage, the
// per-slot helpers above could match the math while the annotator
// silently dropped the scaling.
TEST(SdfAnnotateScaling,
     NonIdentityFactorsPropagateThroughScaleAndAnnotateUnderTypicalMtm) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;
  pre.delays[0] = 0;
  mgr.AddPathDelay(pre);

  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH A Z (10) (20))))))
  )", file));

  SdfScaleFactors factors;
  factors.min_factor = 1.6;
  factors.typ_factor = 1.4;
  factors.max_factor = 1.2;
  SdfFile scaled = ScaleSdfFile(file, SdfScaleType::kFromMtm, factors);
  AnnotateSdfToManager(scaled, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.delays[0], 14u);  // typ_val(10) * 1.4
  EXPECT_EQ(pd.delays[1], 28u);  // typ_val(20) * 1.4
}

// §32.9 Table 32-6 + Table 32-5 composition: FROM_MAXIMUM derives
// each slot of the scaled triplet from the input's max value, and
// MINIMUM picks the min slot of that scaled triplet. With factors
// 2:3:4, an input value of (1, 2, 5) becomes (5*2, 5*3, 5*4) =
// (10, 15, 20); MINIMUM then selects 10. Pins down the order of
// scaling-then-MTM-select on a non-FROM_MTM scale_type.
TEST(SdfAnnotateScaling,
     FromMaximumScaleTypeWithMinimumMtmInstallsMaxScaledByMinFactor) {
  SpecifyManager mgr;
  PathDelay pre;
  pre.src_port = "A";
  pre.dst_port = "Z";
  pre.delay_count = 1;
  pre.delays[0] = 0;
  mgr.AddPathDelay(pre);

  SdfFile file;
  {
    SdfCell cell;
    cell.cell_type = "buf";
    cell.instance = "u1";
    SdfIopath io;
    io.src_port = "A";
    io.dst_port = "Z";
    io.rise.min_val = 1;
    io.rise.typ_val = 2;
    io.rise.max_val = 5;
    io.fall.min_val = 1;
    io.fall.typ_val = 2;
    io.fall.max_val = 5;
    cell.iopaths.push_back(io);
    file.cells.push_back(cell);
  }

  SdfScaleFactors factors;
  factors.min_factor = 2.0;
  factors.typ_factor = 3.0;
  factors.max_factor = 4.0;
  SdfFile scaled = ScaleSdfFile(file, SdfScaleType::kFromMaximum, factors);
  AnnotateSdfToManager(scaled, mgr, SdfMtm::kMinimum);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.delays[0], 10u);  // max(5) * min_factor(2)
  EXPECT_EQ(pd.delays[1], 10u);
}

// §32.9 paragraph "log_file": "Each individual annotation of timing
// data from the SDF file results in an entry in the log file." For a
// file with three IOPATH annotations across one cell, the log writer
// must produce exactly three entries — one per annotation — so a
// downstream reader can count what was applied.
TEST(SdfAnnotationLog, OneEntryWrittenPerIndividualAnnotation) {
  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE
          (IOPATH A Z (10) (20))
          (IOPATH B Z (5)  (8))
          (IOPATH C Z (1)  (2))))))
  )", file));

  std::string log_path = "/tmp/sdf_annotate_log_test.log";
  std::remove(log_path.c_str());
  EXPECT_TRUE(WriteSdfAnnotationLog(file, log_path));

  std::ifstream in(log_path);
  ASSERT_TRUE(in.is_open());
  size_t line_count = 0;
  std::string line;
  while (std::getline(in, line)) {
    if (!line.empty()) ++line_count;
  }
  EXPECT_EQ(line_count, 3u);
  std::remove(log_path.c_str());
}

// §32.9 paragraph "log_file": each backannotation category contributes
// "an entry" — IOPATH, INTERCONNECT, specparams (LABEL), pulse limits
// (PATHPULSE), and timing checks each represent an "individual
// annotation". A file mixing all five categories must produce a log
// entry per construct; without the cross-category coverage a logger
// that only handled IOPATH would still pass the count test above.
TEST(SdfAnnotationLog, EveryBackannotationCategoryContributesAnEntry) {
  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "mix")
        (INSTANCE u1)
        (DELAY (ABSOLUTE
          (IOPATH A Z (10))
          (INTERCONNECT s d (5))
          (PATHPULSE A Z (3))))
        (TIMINGCHECK (SETUP D (posedge CLK) (4)))
        (LABEL (ABSOLUTE (tHold 11)))))
  )", file));

  std::string log_path = "/tmp/sdf_annotate_log_test_categories.log";
  std::remove(log_path.c_str());
  EXPECT_TRUE(WriteSdfAnnotationLog(file, log_path));

  std::ifstream in(log_path);
  ASSERT_TRUE(in.is_open());
  std::stringstream contents;
  contents << in.rdbuf();
  std::string text = contents.str();
  // One line per annotation: IOPATH, INTERCONNECT, PATHPULSE,
  // TIMINGCHECK, SPECPARAM. The exact format is internal; the
  // observable §32.9 rule is that each category gets a line, so we
  // probe for keyword markers per category.
  EXPECT_NE(text.find("IOPATH"), std::string::npos);
  EXPECT_NE(text.find("INTERCONNECT"), std::string::npos);
  EXPECT_NE(text.find("PATHPULSE"), std::string::npos);
  EXPECT_NE(text.find("TIMINGCHECK"), std::string::npos);
  EXPECT_NE(text.find("SPECPARAM"), std::string::npos);
  std::remove(log_path.c_str());
}

// §32.9 paragraph "log_file": the log_file argument is optional. When
// the caller supplies an empty path string (the LRM-equivalent of
// omitting the argument), the writer must succeed without producing a
// file so the surrounding annotation flow stays uniform regardless of
// whether the caller wanted a log.
TEST(SdfAnnotationLog, EmptyPathIsANoOpAndReportsSuccess) {
  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH A Z (10))))))
  )", file));
  EXPECT_TRUE(WriteSdfAnnotationLog(file, ""));
}

// §32.9 paragraph "log_file": "Each individual annotation of timing
// data from the SDF file results in an entry in the log file." A
// file with no annotations yields no individual annotations, so the
// log file must contain zero entries — but the writer must still
// succeed because there is nothing pathological about an empty file.
// Without this edge case, a writer that crashed on zero cells or
// silently failed (returning false) would still pass the count test
// for the populated file above.
TEST(SdfAnnotationLog, EmptySdfFileProducesZeroEntriesAndStillSucceeds) {
  SdfFile file;
  std::string log_path = "/tmp/sdf_annotate_log_empty.log";
  std::remove(log_path.c_str());
  EXPECT_TRUE(WriteSdfAnnotationLog(file, log_path));
  std::ifstream in(log_path);
  ASSERT_TRUE(in.is_open());
  size_t line_count = 0;
  std::string line;
  while (std::getline(in, line)) {
    if (!line.empty()) ++line_count;
  }
  EXPECT_EQ(line_count, 0u);
  std::remove(log_path.c_str());
}

// §32.9 paragraph "log_file": when the caller supplied a log_file
// argument the simulator must report the failure rather than
// silently dropping the log entries. A path inside a directory that
// does not exist cannot be created, so the writer must return false
// and surface the error to the caller. Without this, a misconfigured
// log_file argument would invisibly suppress every annotation entry.
TEST(SdfAnnotationLog, UnwritablePathReportsFailureToCaller) {
  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH A Z (10))))))
  )", file));
  // A path inside a non-existent directory cannot be opened for write.
  EXPECT_FALSE(WriteSdfAnnotationLog(
      file, "/tmp/nonexistent_dir_for_sdf_log_test/x.log"));
}

// §32.9 scale_factors paragraph: the scaling pipeline must reach
// every backannotation category, not just IOPATH. With FROM_MTM and
// asymmetric factors, an INTERCONNECT entry must land on the
// manager with the per-slot scaled values. A regression that only
// scaled IOPATH delays (forgetting interconnect entries during
// ScaleSdfFile) would still pass the IOPATH integration test above
// but silently leave interconnect delays unscaled.
TEST(SdfAnnotateScaling,
     NonIdentityFactorsPropagateToInterconnectDelaysUnderTypicalMtm) {
  SpecifyManager mgr;

  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "net")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (INTERCONNECT s d (10))))))
  )", file));

  SdfScaleFactors factors;
  factors.min_factor = 1.6;
  factors.typ_factor = 1.4;
  factors.max_factor = 1.2;
  SdfFile scaled = ScaleSdfFile(file, SdfScaleType::kFromMtm, factors);
  AnnotateSdfToManager(scaled, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetInterconnectDelays().size(), 1u);
  const auto& ic = mgr.GetInterconnectDelays()[0];
  EXPECT_EQ(ic.rise, 14u);  // typ_val(10) * typ_factor(1.4)
}

// §32.9 scale_factors paragraph: the scaling pipeline must reach
// the specparam backannotation category as well. With FROM_TYPICAL
// and a non-unity typical factor, a LABEL specparam entry must
// install the scaled value on the manager. Companion to the
// interconnect test above; together they pin down scaling for the
// three non-timingcheck backannotation categories §32.2 names.
TEST(SdfAnnotateScaling,
     NonIdentityFactorsPropagateToSpecparamValuesUnderTypicalMtm) {
  SpecifyManager mgr;

  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (LABEL (ABSOLUTE (tHold 10)))))
  )", file));

  SdfScaleFactors factors;
  factors.min_factor = 0.5;
  factors.typ_factor = 2.0;
  factors.max_factor = 0.5;
  SdfFile scaled = ScaleSdfFile(file, SdfScaleType::kFromMtm, factors);
  AnnotateSdfToManager(scaled, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetSpecparamValues().size(), 1u);
  EXPECT_EQ(mgr.GetSpecparamValues()[0].name, "tHold");
  EXPECT_EQ(mgr.GetSpecparamValues()[0].value, 20u);  // 10 * 2.0
}

// §32.9 scale_factors paragraph: the §32.9 text says "scale factors
// to be used while annotating timing values" — timing-check limits
// are timing values too, so an SDF SETUP limit must be scaled
// before it lands on the manager. Without this, scaling would only
// reach the propagation-delay categories and timing checks would
// silently observe unscaled limits.
TEST(SdfAnnotateScaling,
     NonIdentityFactorsPropagateToTimingCheckLimitsUnderTypicalMtm) {
  SpecifyManager mgr;
  TimingCheckEntry pre;
  pre.kind = TimingCheckKind::kSetup;
  pre.ref_signal = "CLK";
  pre.ref_edge = SpecifyEdge::kPosedge;
  pre.data_signal = "D";
  pre.limit = 0;
  mgr.AddTimingCheck(pre);

  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "ff")
        (INSTANCE u1)
        (TIMINGCHECK (SETUP D (posedge CLK) (10)))))
  )", file));

  SdfScaleFactors factors;
  factors.min_factor = 1.0;
  factors.typ_factor = 1.5;
  factors.max_factor = 1.0;
  SdfFile scaled = ScaleSdfFile(file, SdfScaleType::kFromMtm, factors);
  AnnotateSdfToManager(scaled, mgr, SdfMtm::kTypical);

  // §32.4.2 expansion produces $setup and $setuphold-setup-slot from
  // a SETUP construct; whichever of the resulting timing checks the
  // manager landed on, its limit must be 15 (10 * 1.5) — the scaled
  // value rather than the raw 10.
  bool found_scaled = false;
  for (const auto& tc : mgr.GetTimingChecks()) {
    if (tc.limit == 15u) {
      found_scaled = true;
      break;
    }
  }
  EXPECT_TRUE(found_scaled);
}

// §32.9 scale_factors paragraph: scaling must not perturb the cell
// identity carried by the parsed SdfFile — only the numeric delay
// values change. ScaleSdfFile must preserve cell_type and instance
// strings so the downstream scope filter (§32.6) still locates the
// right cells after scaling. A regression that constructed the
// scaled file from default-initialised cells would lose those
// identifiers and break every test that combines scaling with
// scope filtering.
TEST(SdfScaleFile, PreservesCellTypeAndInstanceMetadata) {
  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buffer_x4")
        (INSTANCE u1/dut)
        (DELAY (ABSOLUTE (IOPATH A Z (10))))))
  )", file));

  SdfScaleFactors factors;
  factors.typ_factor = 2.0;
  SdfFile scaled = ScaleSdfFile(file, SdfScaleType::kFromMtm, factors);

  ASSERT_EQ(scaled.cells.size(), 1u);
  EXPECT_EQ(scaled.cells[0].cell_type, "buffer_x4");
  EXPECT_EQ(scaled.cells[0].instance, "u1/dut");
  ASSERT_EQ(scaled.cells[0].iopaths.size(), 1u);
  EXPECT_EQ(scaled.cells[0].iopaths[0].rise.typ_val, 20u);
}

// §32.9 scale_factors paragraph: the SDF rvalue convention treats a
// single bare value as a triplet (n, n, n). The parser must
// broadcast a single-real input across all three factor slots so a
// caller passing "1.6" sees the same min/typ/max multiplier on
// every slot. Without coverage, the parser could silently leave the
// missing slots at their prior values.
TEST(SdfScaleFactorsParser, SingleValueBroadcastsAcrossAllThreeFactorSlots) {
  SdfScaleFactors out;
  EXPECT_TRUE(ParseSdfScaleFactors("1.6", out));
  EXPECT_DOUBLE_EQ(out.min_factor, 1.6);
  EXPECT_DOUBLE_EQ(out.typ_factor, 1.6);
  EXPECT_DOUBLE_EQ(out.max_factor, 1.6);
}

// §32.9 scale_factors paragraph: the SDF rvalue convention treats a
// "min:typ" pair (no max) as broadcasting the typical value into the
// max slot. Pins down the partial-triplet semantics so a caller
// that only wants to scale min/typ differently — leaving max at the
// typical multiplier — gets the right behaviour without specifying
// a redundant max.
TEST(SdfScaleFactorsParser, TwoValuePartialTripletBroadcastsTypicalIntoMax) {
  SdfScaleFactors out;
  EXPECT_TRUE(ParseSdfScaleFactors("1.6:1.4", out));
  EXPECT_DOUBLE_EQ(out.min_factor, 1.6);
  EXPECT_DOUBLE_EQ(out.typ_factor, 1.4);
  EXPECT_DOUBLE_EQ(out.max_factor, 1.4);
}

// §32.9 scale_factors paragraph: a malformed scale_factors string
// (one that does not begin with a real number where a number is
// expected) must be rejected so the surrounding $sdf_annotate
// invocation can fall back to the LRM-stated default rather than
// silently using uninitialised or garbage multipliers. Without an
// error signal the caller has no way to distinguish a malformed
// argument from a successful parse.
TEST(SdfScaleFactorsParser, MalformedInputIsRejectedAndDoesNotMutateDefaults) {
  SdfScaleFactors out;
  EXPECT_FALSE(ParseSdfScaleFactors("not-a-number", out));
  EXPECT_DOUBLE_EQ(out.min_factor, 1.0);
  EXPECT_DOUBLE_EQ(out.typ_factor, 1.0);
  EXPECT_DOUBLE_EQ(out.max_factor, 1.0);
}

// §32.9 scale_factors paragraph: a zero scale factor is a degenerate
// but valid input — a caller can use it to clamp every annotated
// value to zero. The scaling pipeline must produce zero rather than
// crash, divide-by-zero, or fall back to the input value. Without
// this, an off-by-one in the rounding helper that special-cased
// zero (e.g. via std::max with a positive guard) could produce
// non-zero output.
TEST(SdfScaling, ZeroFactorClampsScaledValueToZero) {
  SdfDelayValue v;
  v.min_val = 100;
  v.typ_val = 200;
  v.max_val = 300;
  SdfScaleFactors f;
  f.min_factor = 0.0;
  f.typ_factor = 0.0;
  f.max_factor = 0.0;
  auto out = ApplySdfScaling(v, SdfScaleType::kFromMtm, f);
  EXPECT_EQ(out.min_val, 0u);
  EXPECT_EQ(out.typ_val, 0u);
  EXPECT_EQ(out.max_val, 0u);
}

// §32.9 paragraph 2 ("the $sdf_annotate system task reads timing
// data from an SDF file into a specified region of the design"):
// because the LRM's "more than one SDF file can be annotated"
// extension to this task is described in §32.6 sentence 1, the
// recording API must let two successive AnnotateSdf calls coexist
// — the second must not drop the first. Pins the §32.9 entry-point
// rule that each call records a separate request without disturbing
// prior recordings.
TEST(SdfAnnotateRequest, MultipleCallsRecordSeparateRequestsInOrder) {
  SpecifyManager mgr;
  mgr.AnnotateSdf({"first.sdf", "top.dut1"});
  mgr.AnnotateSdf({"second.sdf", "top.dut2"});
  ASSERT_EQ(mgr.GetSdfAnnotations().size(), 2u);
  EXPECT_EQ(mgr.GetSdfAnnotations()[0].sdf_file, "first.sdf");
  EXPECT_EQ(mgr.GetSdfAnnotations()[0].scope, "top.dut1");
  EXPECT_EQ(mgr.GetSdfAnnotations()[1].sdf_file, "second.sdf");
  EXPECT_EQ(mgr.GetSdfAnnotations()[1].scope, "top.dut2");
}

// §32.9 module_instance paragraph: when omitted, "the SDF annotator
// uses the module containing the call ... as the module_instance".
// Until the runtime $sdf_annotate dispatch is wired up, the closest
// observable contract is that the recording API can carry an empty
// scope (signalling "no explicit scope") without dropping the
// sdf_file. Pins down that the recording side preserves the
// distinction between "scope omitted" and "explicit empty scope".
TEST(SdfAnnotateRequest, EmptyScopePreservesSdfFileForCallerDefaulting) {
  SpecifyManager mgr;
  mgr.AnnotateSdf({"timing.sdf", ""});
  ASSERT_EQ(mgr.GetSdfAnnotations().size(), 1u);
  EXPECT_EQ(mgr.GetSdfAnnotations()[0].sdf_file, "timing.sdf");
  EXPECT_TRUE(mgr.GetSdfAnnotations()[0].scope.empty());
}

// §32.9 mtm_spec paragraph last sentence: "This overrides any
// MTM_SPEC keywords in the configuration file." With both layers
// non-empty and naming different slots, the resolver must keep the
// explicit argument's value rather than the config-file's. Pins down
// the override direction so a regression that swapped precedence (or
// silently merged the two) is caught.
TEST(SdfAnnotateArgResolver,
     ExplicitMtmSpecOverridesConfigFileKeyword) {
  SdfAnnotateConfig config;
  config.mtm_spec = "MAXIMUM";
  auto out = ResolveSdfAnnotateArgs("MINIMUM", "", "", config);
  EXPECT_EQ(out.mtm, SdfMtmKeyword::kMinimum);
}

// §32.9 mtm_spec paragraph: when the explicit argument is omitted
// (empty string, the LRM equivalent of leaving the position blank in
// the call), the config-file value must be honoured rather than
// silently falling through to the LRM default. Without this leg, an
// implementation could drop the config-file value entirely, leaving
// every invocation that relied on the config file behaving as if
// the config did not exist.
TEST(SdfAnnotateArgResolver,
     EmptyExplicitMtmSpecFallsThroughToConfigKeyword) {
  SdfAnnotateConfig config;
  config.mtm_spec = "MAXIMUM";
  auto out = ResolveSdfAnnotateArgs("", "", "", config);
  EXPECT_EQ(out.mtm, SdfMtmKeyword::kMaximum);
}

// §32.9 mtm_spec paragraph + Table 32-5 default: with both explicit
// and config-file layers empty, the resolver must produce the
// LRM-stated default (TOOL_CONTROL) so a caller that omitted the
// argument and supplied no config file behaves identically to one
// who explicitly named "TOOL_CONTROL".
TEST(SdfAnnotateArgResolver,
     EmptyExplicitAndEmptyConfigYieldsToolControlDefault) {
  SdfAnnotateConfig config;
  auto out = ResolveSdfAnnotateArgs("", "", "", config);
  EXPECT_EQ(out.mtm, SdfMtmKeyword::kToolControl);
}

// §32.9 scale_factors paragraph last sentence: "The scale_factors
// argument overrides any SCALE_FACTORS keywords in the configuration
// file." With distinct values per slot in both layers, the resolver
// must keep the explicit triplet so a downstream MTM-select observes
// the explicit multipliers, not the config-file ones.
TEST(SdfAnnotateArgResolver,
     ExplicitScaleFactorsOverrideConfigFileKeyword) {
  SdfAnnotateConfig config;
  config.scale_factors = "2.0:3.0:4.0";
  auto out = ResolveSdfAnnotateArgs("", "1.6:1.4:1.2", "", config);
  EXPECT_DOUBLE_EQ(out.factors.min_factor, 1.6);
  EXPECT_DOUBLE_EQ(out.factors.typ_factor, 1.4);
  EXPECT_DOUBLE_EQ(out.factors.max_factor, 1.2);
}

// §32.9 scale_factors paragraph: with the explicit argument empty,
// the config-file SCALE_FACTORS keyword takes effect. Pins down the
// fallback leg of the override rule so a regression that always
// returned the LRM identity-triplet on an empty explicit arg would
// silently lose the config-file values.
TEST(SdfAnnotateArgResolver,
     EmptyExplicitScaleFactorsFallsThroughToConfigKeyword) {
  SdfAnnotateConfig config;
  config.scale_factors = "2.0:3.0:4.0";
  auto out = ResolveSdfAnnotateArgs("", "", "", config);
  EXPECT_DOUBLE_EQ(out.factors.min_factor, 2.0);
  EXPECT_DOUBLE_EQ(out.factors.typ_factor, 3.0);
  EXPECT_DOUBLE_EQ(out.factors.max_factor, 4.0);
}

// §32.9 scale_type paragraph last sentence: "This overrides any
// SCALE_TYPE keywords in the configuration file." With the two layers
// naming different rows of Table 32-6, the resolver must keep the
// explicit value so the downstream scaling broadcast is computed
// against the explicit row.
TEST(SdfAnnotateArgResolver,
     ExplicitScaleTypeOverridesConfigFileKeyword) {
  SdfAnnotateConfig config;
  config.scale_type = "FROM_MAXIMUM";
  auto out = ResolveSdfAnnotateArgs("", "", "FROM_MINIMUM", config);
  EXPECT_EQ(out.scale_type, SdfScaleType::kFromMinimum);
}

// §32.9 scale_type paragraph: with the explicit argument empty, the
// config-file SCALE_TYPE keyword takes effect. Pins down the fallback
// leg.
TEST(SdfAnnotateArgResolver,
     EmptyExplicitScaleTypeFallsThroughToConfigKeyword) {
  SdfAnnotateConfig config;
  config.scale_type = "FROM_MAXIMUM";
  auto out = ResolveSdfAnnotateArgs("", "", "", config);
  EXPECT_EQ(out.scale_type, SdfScaleType::kFromMaximum);
}

// §32.9 scale_type paragraph + Table 32-6 default: with both layers
// empty the resolver must produce FROM_MTM, the LRM-stated default.
TEST(SdfAnnotateArgResolver,
     EmptyExplicitAndEmptyConfigYieldsFromMtmDefault) {
  SdfAnnotateConfig config;
  auto out = ResolveSdfAnnotateArgs("", "", "", config);
  EXPECT_EQ(out.scale_type, SdfScaleType::kFromMtm);
}

// §32.9 R14/R19/R22 composition: a single invocation that exercises
// all three override rules at once must produce the explicit values
// for every category. Without the composite test, an implementation
// that handled R14 and R22 correctly but silently dropped R19's
// override (or vice versa) would still pass the per-category tests
// above.
TEST(SdfAnnotateArgResolver,
     ExplicitArgsOverrideEveryConfigKeywordSimultaneously) {
  SdfAnnotateConfig config;
  config.mtm_spec = "MAXIMUM";
  config.scale_factors = "2.0:3.0:4.0";
  config.scale_type = "FROM_MAXIMUM";
  auto out = ResolveSdfAnnotateArgs("MINIMUM", "1.6:1.4:1.2",
                                     "FROM_MINIMUM", config);
  EXPECT_EQ(out.mtm, SdfMtmKeyword::kMinimum);
  EXPECT_DOUBLE_EQ(out.factors.min_factor, 1.6);
  EXPECT_DOUBLE_EQ(out.factors.typ_factor, 1.4);
  EXPECT_DOUBLE_EQ(out.factors.max_factor, 1.2);
  EXPECT_EQ(out.scale_type, SdfScaleType::kFromMinimum);
}

// §32.9 paragraph "log_file": "Each individual annotation of timing
// data from the SDF file results in an entry in the log file." An
// IOPATH entry must therefore name its rise and fall delays — those
// are the timing data being annotated. A regression that wrote only
// the construct kind and port pair (without the actual delay values)
// would still produce one line per annotation but lose the "timing
// data" half of the rule.
TEST(SdfAnnotationLog, IopathEntryRecordsRiseAndFallDelayValues) {
  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH A Z (15) (27))))))
  )", file));

  std::string log_path = "/tmp/sdf_annotate_log_iopath_values.log";
  std::remove(log_path.c_str());
  EXPECT_TRUE(WriteSdfAnnotationLog(file, log_path));

  std::ifstream in(log_path);
  std::stringstream contents;
  contents << in.rdbuf();
  std::string text = contents.str();
  EXPECT_NE(text.find("IOPATH"), std::string::npos);
  EXPECT_NE(text.find("rise=15"), std::string::npos);
  EXPECT_NE(text.find("fall=27"), std::string::npos);
  std::remove(log_path.c_str());
}

// §32.9 paragraph "log_file" applied to the timing-check category:
// the entry must name the limit value the SDF file installed, not
// just the construct kind. Without this, a logger that omitted the
// limit value for timing checks would conceal which checks were
// updated and to what value.
TEST(SdfAnnotationLog, TimingCheckEntryRecordsLimitValue) {
  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "ff")
        (INSTANCE u1)
        (TIMINGCHECK (SETUP D (posedge CLK) (42)))))
  )", file));

  std::string log_path = "/tmp/sdf_annotate_log_tc_limit.log";
  std::remove(log_path.c_str());
  EXPECT_TRUE(WriteSdfAnnotationLog(file, log_path));

  std::ifstream in(log_path);
  std::stringstream contents;
  contents << in.rdbuf();
  std::string text = contents.str();
  EXPECT_NE(text.find("TIMINGCHECK"), std::string::npos);
  EXPECT_NE(text.find("limit=42"), std::string::npos);
  std::remove(log_path.c_str());
}

// §32.9 paragraph "log_file" applied to the specparam category: the
// entry must record the new value the LABEL section supplied. The
// SPECPARAM substring presence is already covered by an earlier
// per-category test, but without an explicit value-bearing assertion
// a regression that emitted the name without its updated value would
// still pass that earlier test.
TEST(SdfAnnotationLog, SpecparamEntryRecordsNewValue) {
  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (LABEL (ABSOLUTE (tHold 99)))))
  )", file));

  std::string log_path = "/tmp/sdf_annotate_log_specparam_value.log";
  std::remove(log_path.c_str());
  EXPECT_TRUE(WriteSdfAnnotationLog(file, log_path));

  std::ifstream in(log_path);
  std::stringstream contents;
  contents << in.rdbuf();
  std::string text = contents.str();
  EXPECT_NE(text.find("SPECPARAM"), std::string::npos);
  EXPECT_NE(text.find("tHold"), std::string::npos);
  EXPECT_NE(text.find("value=99"), std::string::npos);
  std::remove(log_path.c_str());
}

}  // namespace
