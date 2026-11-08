#include <gtest/gtest.h>

#include <cstdio>
#include <fstream>
#include <sstream>
#include <string>

#include "simulator/sdf_parser.h"

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

TEST(SdfMtmKeyword, UnknownStringIsRejectedAndLeavesOutputUntouched) {
  SdfMtmKeyword out = SdfMtmKeyword::kTypical;
  EXPECT_FALSE(ParseSdfMtmKeyword("BOGUS", out));
  EXPECT_EQ(out, SdfMtmKeyword::kTypical);
}

TEST(SdfScaleTypeParser, UnknownStringIsRejectedAndLeavesOutputUntouched) {
  SdfScaleType out = SdfScaleType::kFromTypical;
  EXPECT_FALSE(ParseSdfScaleType("FROM_NOWHERE", out));
  EXPECT_EQ(out, SdfScaleType::kFromTypical);
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
          (DEVICE Z (7))
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
  EXPECT_NE(text.find("DEVICE"), std::string::npos);
  EXPECT_NE(text.find("PATHPULSE"), std::string::npos);
  EXPECT_NE(text.find("TIMINGCHECK"), std::string::npos);
  EXPECT_NE(text.find("SPECPARAM"), std::string::npos);
  std::remove(log_path.c_str());
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

TEST(SdfScaling, ScalingKeepsEachMembersSign) {
  SdfDelayValue v;
  v.min_val = 1;
  v.typ_val = 2;
  v.max_val = 3;
  v.typ_negative = true;
  SdfScaleFactors f;
  auto mtm = ApplySdfScaling(v, SdfScaleType::kFromMtm, f);
  EXPECT_FALSE(mtm.min_negative);
  EXPECT_TRUE(mtm.typ_negative);
  EXPECT_FALSE(mtm.max_negative);
  EXPECT_EQ(mtm.typ_val, 2u);
  auto typ = ApplySdfScaling(v, SdfScaleType::kFromTypical, f);
  EXPECT_TRUE(typ.min_negative);
  EXPECT_TRUE(typ.typ_negative);
  EXPECT_TRUE(typ.max_negative);
}

TEST(SdfRealValues, RealValuesAndTheTimescaleHeaderAreRead) {
  SdfFile file;
  ASSERT_TRUE(ParseSdf(R"(
    (DELAYFILE
      (TIMESCALE 100ps)
      (CELL (CELLTYPE "buf") (INSTANCE u1)
        (DELAY (ABSOLUTE (IOPATH A Z (2.5) (1.3))))))
  )",
                       file));
  EXPECT_TRUE(file.unannotatable.empty());
  EXPECT_DOUBLE_EQ(file.timescale_seconds, 100e-12);
  ASSERT_EQ(file.cells.size(), 1u);
  ASSERT_EQ(file.cells[0].iopaths.size(), 1u);
  EXPECT_DOUBLE_EQ(file.cells[0].iopaths[0].rise.typ_real, 2.5);
  EXPECT_DOUBLE_EQ(file.cells[0].iopaths[0].fall.typ_real, 1.3);

  SdfFile spaced;
  ASSERT_TRUE(ParseSdf("(DELAYFILE (TIMESCALE 1 ns))", spaced));
  EXPECT_DOUBLE_EQ(spaced.timescale_seconds, 1e-9);
  SdfFile none;
  ASSERT_TRUE(ParseSdf("(DELAYFILE)", none));
  EXPECT_DOUBLE_EQ(none.timescale_seconds, 0.0);
}

TEST(SdfRealValues, ScalingReadsTheExactMagnitude) {
  SdfDelayValue v;
  v.min_val = v.typ_val = v.max_val = 3;
  v.min_real = v.typ_real = v.max_real = 2.5;
  SdfScaleFactors f;
  f.min_factor = f.typ_factor = f.max_factor = 1000.0;
  auto out = ApplySdfScaling(v, SdfScaleType::kFromMtm, f);
  EXPECT_EQ(out.typ_val, 2500u);
}

TEST(SdfScaling, PulsePercentagesAreNotScaled) {
  SdfFile file;
  ASSERT_TRUE(ParseSdf(
      "(DELAYFILE (CELL (CELLTYPE \"m\") (INSTANCE u) (DELAY (ABSOLUTE "
      "(PATHPULSEPERCENT a y (25) (50)) (PATHPULSE a y (2) (3))))))",
      file));
  SdfScaleFactors factors;
  ASSERT_TRUE(ParseSdfScaleFactors("2:2:2", factors));
  const SdfFile kScaled = ScaleSdfFile(file, SdfScaleType::kFromMtm, factors);
  ASSERT_EQ(kScaled.cells.size(), 1u);
  ASSERT_EQ(kScaled.cells[0].pulse_limits.size(), 2u);
  EXPECT_EQ(kScaled.cells[0].pulse_limits[0].reject.typ_val, 25u);
  EXPECT_EQ(kScaled.cells[0].pulse_limits[0].error.typ_val, 50u);
  EXPECT_EQ(kScaled.cells[0].pulse_limits[1].reject.typ_val, 4u);
  EXPECT_EQ(kScaled.cells[0].pulse_limits[1].error.typ_val, 6u);
}

}  // namespace
