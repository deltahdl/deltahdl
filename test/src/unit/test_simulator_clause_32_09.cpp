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

TEST(SdfMtmKeyword, ToolControlReturnsCallerSuppliedDefaultMtm) {
  EXPECT_EQ(ResolveSdfMtm(SdfMtmKeyword::kToolControl, SdfMtm::kMinimum),
            SdfMtm::kMinimum);
  EXPECT_EQ(ResolveSdfMtm(SdfMtmKeyword::kToolControl, SdfMtm::kTypical),
            SdfMtm::kTypical);
  EXPECT_EQ(ResolveSdfMtm(SdfMtmKeyword::kToolControl, SdfMtm::kMaximum),
            SdfMtm::kMaximum);
}

TEST(SdfMtmKeyword, NamedKeywordOverridesCallerSuppliedDefault) {
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

TEST(SdfScaleFactors, DefaultMultipliersAreOnePointZero) {
  SdfScaleFactors sf;
  EXPECT_DOUBLE_EQ(sf.min_factor, 1.0);
  EXPECT_DOUBLE_EQ(sf.typ_factor, 1.0);
  EXPECT_DOUBLE_EQ(sf.max_factor, 1.0);
}

TEST(SdfScaleFactorsParser, ColonSeparatedTripletDecomposesIntoOrderedFactors) {
  SdfScaleFactors out;
  EXPECT_TRUE(ParseSdfScaleFactors("1.6:1.4:1.2", out));
  EXPECT_DOUBLE_EQ(out.min_factor, 1.6);
  EXPECT_DOUBLE_EQ(out.typ_factor, 1.4);
  EXPECT_DOUBLE_EQ(out.max_factor, 1.2);
}

TEST(SdfScaleFactorsParser, EmptyStringLeavesDefaultsInPlace) {
  SdfScaleFactors out;
  out.min_factor = 9.0;
  out.typ_factor = 9.0;
  out.max_factor = 9.0;
  EXPECT_TRUE(ParseSdfScaleFactors("", out));
  EXPECT_DOUBLE_EQ(out.min_factor, 1.0);
  EXPECT_DOUBLE_EQ(out.typ_factor, 1.0);
  EXPECT_DOUBLE_EQ(out.max_factor, 1.0);
}

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
  EXPECT_EQ(out.min_val, 16u);
  EXPECT_EQ(out.typ_val, 28u);
  EXPECT_EQ(out.max_val, 36u);
}

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
  EXPECT_EQ(out.min_val, 48u);
  EXPECT_EQ(out.typ_val, 42u);
  EXPECT_EQ(out.max_val, 36u);
}

TEST(SdfScaling, FromMinimumDerivesEverySlotFromTheMinimumValue) {
  SdfDelayValue v;
  v.min_val = 10;
  v.typ_val = 20;
  v.max_val = 30;
  SdfScaleFactors f;
  f.min_factor = 1.6;
  f.typ_factor = 1.4;
  f.max_factor = 1.2;
  auto out = ApplySdfScaling(v, SdfScaleType::kFromMinimum, f);
  EXPECT_EQ(out.min_val, 16u);
  EXPECT_EQ(out.typ_val, 14u);
  EXPECT_EQ(out.max_val, 12u);
}

TEST(SdfScaling, FromTypicalDerivesEverySlotFromTheTypicalValue) {
  SdfDelayValue v;
  v.min_val = 10;
  v.typ_val = 20;
  v.max_val = 30;
  SdfScaleFactors f;
  f.min_factor = 1.6;
  f.typ_factor = 1.4;
  f.max_factor = 1.2;
  auto out = ApplySdfScaling(v, SdfScaleType::kFromTypical, f);
  EXPECT_EQ(out.min_val, 32u);
  EXPECT_EQ(out.typ_val, 28u);
  EXPECT_EQ(out.max_val, 24u);
}

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
  )",
                       file));

  SdfScaleFactors factors;
  factors.min_factor = 1.6;
  factors.typ_factor = 1.4;
  factors.max_factor = 1.2;
  SdfFile scaled = ScaleSdfFile(file, SdfScaleType::kFromMtm, factors);
  AnnotateSdfToManager(scaled, mgr, SdfMtm::kTypical);

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  const auto& pd = mgr.GetPathDelays()[0];
  EXPECT_EQ(pd.delays[0], 14u);
  EXPECT_EQ(pd.delays[1], 28u);
}

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
  EXPECT_EQ(pd.delays[0], 10u);
  EXPECT_EQ(pd.delays[1], 10u);
}

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
  )",
                       file));

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
  )",
                       file));

  std::string log_path = "/tmp/sdf_annotate_log_test_categories.log";
  std::remove(log_path.c_str());
  EXPECT_TRUE(WriteSdfAnnotationLog(file, log_path));

  std::ifstream in(log_path);
  ASSERT_TRUE(in.is_open());
  std::stringstream contents;
  contents << in.rdbuf();
  std::string text = contents.str();

  EXPECT_NE(text.find("IOPATH"), std::string::npos);
  EXPECT_NE(text.find("INTERCONNECT"), std::string::npos);
  EXPECT_NE(text.find("PATHPULSE"), std::string::npos);
  EXPECT_NE(text.find("TIMINGCHECK"), std::string::npos);
  EXPECT_NE(text.find("SPECPARAM"), std::string::npos);
  std::remove(log_path.c_str());
}

TEST(SdfAnnotationLog, EmptyPathIsANoOpAndReportsSuccess) {
  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH A Z (10))))))
  )",
                       file));
  EXPECT_TRUE(WriteSdfAnnotationLog(file, ""));
}

TEST(SdfAnnotationLog, UnwritablePathReportsFailureToCaller) {
  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL
        (CELLTYPE "buf")
        (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH A Z (10))))))
  )",
                       file));

  EXPECT_FALSE(WriteSdfAnnotationLog(
      file, "/tmp/nonexistent_dir_for_sdf_log_test/x.log"));
}

TEST(SdfScaleFactorsParser, SingleValueBroadcastsAcrossAllThreeFactorSlots) {
  SdfScaleFactors out;
  EXPECT_TRUE(ParseSdfScaleFactors("1.6", out));
  EXPECT_DOUBLE_EQ(out.min_factor, 1.6);
  EXPECT_DOUBLE_EQ(out.typ_factor, 1.6);
  EXPECT_DOUBLE_EQ(out.max_factor, 1.6);
}

TEST(SdfScaleFactorsParser, TwoValuePartialTripletBroadcastsTypicalIntoMax) {
  SdfScaleFactors out;
  EXPECT_TRUE(ParseSdfScaleFactors("1.6:1.4", out));
  EXPECT_DOUBLE_EQ(out.min_factor, 1.6);
  EXPECT_DOUBLE_EQ(out.typ_factor, 1.4);
  EXPECT_DOUBLE_EQ(out.max_factor, 1.4);
}

TEST(SdfScaleFactorsParser, MalformedInputIsRejectedAndDoesNotMutateDefaults) {
  SdfScaleFactors out;
  EXPECT_FALSE(ParseSdfScaleFactors("not-a-number", out));
  EXPECT_DOUBLE_EQ(out.min_factor, 1.0);
  EXPECT_DOUBLE_EQ(out.typ_factor, 1.0);
  EXPECT_DOUBLE_EQ(out.max_factor, 1.0);
}

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

TEST(SdfAnnotateRequest, EmptyScopePreservesSdfFileForCallerDefaulting) {
  SpecifyManager mgr;
  mgr.AnnotateSdf({"timing.sdf", ""});
  ASSERT_EQ(mgr.GetSdfAnnotations().size(), 1u);
  EXPECT_EQ(mgr.GetSdfAnnotations()[0].sdf_file, "timing.sdf");
  EXPECT_TRUE(mgr.GetSdfAnnotations()[0].scope.empty());
}

TEST(SdfAnnotateArgResolver, ExplicitMtmSpecOverridesConfigFileKeyword) {
  SdfAnnotateConfig config;
  config.mtm_spec = "MAXIMUM";
  auto out = ResolveSdfAnnotateArgs("MINIMUM", "", "", config);
  EXPECT_EQ(out.mtm, SdfMtmKeyword::kMinimum);
}

TEST(SdfAnnotateArgResolver, EmptyExplicitMtmSpecFallsThroughToConfigKeyword) {
  SdfAnnotateConfig config;
  config.mtm_spec = "MAXIMUM";
  auto out = ResolveSdfAnnotateArgs("", "", "", config);
  EXPECT_EQ(out.mtm, SdfMtmKeyword::kMaximum);
}

TEST(SdfAnnotateArgResolver,
     EmptyExplicitAndEmptyConfigYieldsToolControlDefault) {
  SdfAnnotateConfig config;
  auto out = ResolveSdfAnnotateArgs("", "", "", config);
  EXPECT_EQ(out.mtm, SdfMtmKeyword::kToolControl);
}

TEST(SdfAnnotateArgResolver, ExplicitScaleFactorsOverrideConfigFileKeyword) {
  SdfAnnotateConfig config;
  config.scale_factors = "2.0:3.0:4.0";
  auto out = ResolveSdfAnnotateArgs("", "1.6:1.4:1.2", "", config);
  EXPECT_DOUBLE_EQ(out.factors.min_factor, 1.6);
  EXPECT_DOUBLE_EQ(out.factors.typ_factor, 1.4);
  EXPECT_DOUBLE_EQ(out.factors.max_factor, 1.2);
}

TEST(SdfAnnotateArgResolver,
     EmptyExplicitScaleFactorsFallsThroughToConfigKeyword) {
  SdfAnnotateConfig config;
  config.scale_factors = "2.0:3.0:4.0";
  auto out = ResolveSdfAnnotateArgs("", "", "", config);
  EXPECT_DOUBLE_EQ(out.factors.min_factor, 2.0);
  EXPECT_DOUBLE_EQ(out.factors.typ_factor, 3.0);
  EXPECT_DOUBLE_EQ(out.factors.max_factor, 4.0);
}

TEST(SdfAnnotateArgResolver, ExplicitScaleTypeOverridesConfigFileKeyword) {
  SdfAnnotateConfig config;
  config.scale_type = "FROM_MAXIMUM";
  auto out = ResolveSdfAnnotateArgs("", "", "FROM_MINIMUM", config);
  EXPECT_EQ(out.scale_type, SdfScaleType::kFromMinimum);
}

TEST(SdfAnnotateArgResolver,
     EmptyExplicitScaleTypeFallsThroughToConfigKeyword) {
  SdfAnnotateConfig config;
  config.scale_type = "FROM_MAXIMUM";
  auto out = ResolveSdfAnnotateArgs("", "", "", config);
  EXPECT_EQ(out.scale_type, SdfScaleType::kFromMaximum);
}

TEST(SdfAnnotateArgResolver, EmptyExplicitAndEmptyConfigYieldsFromMtmDefault) {
  SdfAnnotateConfig config;
  auto out = ResolveSdfAnnotateArgs("", "", "", config);
  EXPECT_EQ(out.scale_type, SdfScaleType::kFromMtm);
}

// mtm_spec selects which member of each min:typ:max triple is annotated.
// A single IOPATH carrying three distinct values lets the annotated delay
// reveal exactly which member the requested mtm picked.
TEST(SdfAnnotateMtmSelection, AnnotatesTheMtmMemberChosenForEachKeyword) {
  const char* sdf = R"(
    (DELAYFILE
      (CELL (CELLTYPE "buf") (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH A Z (1:2:3))))))
  )";

  auto annotate_under = [&](SdfMtm mtm) -> uint64_t {
    SpecifyManager mgr;
    PathDelay pre;
    pre.src_port = "A";
    pre.dst_port = "Z";
    pre.delay_count = 1;
    pre.delays[0] = 0;
    mgr.AddPathDelay(pre);

    SdfFile file;
    EXPECT_TRUE(ParseSdf(sdf, file));
    AnnotateSdfToManager(file, mgr, mtm);
    return mgr.GetPathDelays()[0].delays[0];
  };

  EXPECT_EQ(annotate_under(SdfMtm::kMinimum), 1u);
  EXPECT_EQ(annotate_under(SdfMtm::kTypical), 2u);
  EXPECT_EQ(annotate_under(SdfMtm::kMaximum), 3u);
}

// module_instance names the scope to annotate: only cells at or beneath that
// hierarchy level are touched. Here the scope is an interior node, so its
// descendant cell is annotated while a sibling subtree is left unchanged.
TEST(SdfAnnotateScope, RestrictsAnnotationToInstancesWithinSpecifiedScope) {
  SpecifyManager mgr;
  PathDelay keep;
  keep.src_port = "A";
  keep.dst_port = "Z";
  keep.delay_count = 1;
  keep.delays[0] = 0;
  mgr.AddPathDelay(keep);
  PathDelay drop;
  drop.src_port = "B";
  drop.dst_port = "Y";
  drop.delay_count = 1;
  drop.delays[0] = 0;
  mgr.AddPathDelay(drop);

  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (CELL (CELLTYPE "buf") (INSTANCE top/sub/leaf)
        (DELAY (ABSOLUTE (IOPATH A Z (10)))))
      (CELL (CELLTYPE "buf") (INSTANCE top/other/leaf)
        (DELAY (ABSOLUTE (IOPATH B Y (20))))))
  )",
                       file));

  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical, "top/sub");

  uint64_t az = 999;
  uint64_t by = 999;
  for (const auto& pd : mgr.GetPathDelays()) {
    if (pd.src_port == "A" && pd.dst_port == "Z") az = pd.delays[0];
    if (pd.src_port == "B" && pd.dst_port == "Y") by = pd.delays[0];
  }
  EXPECT_EQ(az, 10u);
  EXPECT_EQ(by, 0u);
}

// Scope matching is by hierarchy level, not raw string prefix: "top/u1" is a
// textual prefix of "top/u1x" but not an ancestor of it, so that cell stays
// outside scope and is not annotated.
TEST(SdfAnnotateScope, ScopeMatchRequiresHierarchySeparatorNotMerePrefix) {
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
      (CELL (CELLTYPE "buf") (INSTANCE top/u1x)
        (DELAY (ABSOLUTE (IOPATH A Z (10))))))
  )",
                       file));

  AnnotateSdfToManager(file, mgr, SdfMtm::kTypical, "top/u1");

  ASSERT_EQ(mgr.GetPathDelays().size(), 1u);
  EXPECT_EQ(mgr.GetPathDelays()[0].delays[0], 0u);
}

}  // namespace
