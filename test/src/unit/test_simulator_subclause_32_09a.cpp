// The readers behind five of the seven operands §32.9 gives $sdf_annotate,
// called directly rather than through a design: ParseSdf for sdf_file,
// ParseSdfMtmKeyword for "mtm_spec", ParseSdfScaleType for "scale_type",
// ParseSdfScaleFactors for "scale_factors" and WriteSdfAnnotationLog for what
// "log_file" receives, together with ApplySdfScaling, which applies what
// "scale_factors" and "scale_type" name to one delay value. All six are
// declared in src/simulator/sdf_parser.h. Calling each directly is what makes a
// failure here name the function that returned the wrong answer, rather than
// the call that reached it.
//
// The calls are in test_simulator_subclause_32_09b.cpp, which writes
// $sdf_annotate into a design's source and runs it. The two files were one
// until #3157, which split them at 997 lines, 3 short of the maximum
// assert-no-oversized-source-files enforces.

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

}  // namespace
