#include <gtest/gtest.h>

#include <cstdint>
#include <fstream>
#include <ios>
#include <string>
#include <vector>

#include "driver/cli_options.h"
#include "fixture_simulator.h"
#include "helpers_command_line.h"
#include "helpers_sdf_delay_mapping.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"

using namespace delta;

namespace {

PathDelay MakePathWithUniformDelay(uint64_t value) {
  PathDelay pd;
  pd.delay_count = 1;
  for (int i = 0; i < 12; ++i) pd.delays[i] = value;
  InitDefaultPulseLimits(pd);
  return pd;
}

TEST(SdfPulseLimitAnnotation, RejectOnlyMirrorsToError) {
  PathDelay pd = MakePathWithUniformDelay(40);
  ApplySdfPulseLimits(pd, 6, false, 0);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 6u);
    EXPECT_EQ(pd.error_limit[i], 6u);
  }
}

TEST(SdfPulseLimitAnnotation, PropagationDelaysPreserved) {
  PathDelay pd = MakePathWithUniformDelay(40);
  ApplySdfPulseLimits(pd, 3, true, 9);
  for (int i = 0; i < 12; ++i) EXPECT_EQ(pd.delays[i], 40u);
}

TEST(SdfPulseLimitAnnotation, SdfOverridesPathpulseValues) {
  PathDelay pd = MakePathWithUniformDelay(40);
  ApplyPulseControlOverride(pd, 2, true, 7);
  ApplySdfPulseLimits(pd, 11, true, 13);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 11u);
    EXPECT_EQ(pd.error_limit[i], 13u);
  }
}

TEST(SdfPulseLimitAnnotation, SdfOverridesGlobalInvocationLimits) {
  PathDelay pd = MakePathWithUniformDelay(100);
  ApplyGlobalPulseLimits(pd, 50, 75);
  ApplySdfPulseLimits(pd, 4, true, 8);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 4u);
    EXPECT_EQ(pd.error_limit[i], 8u);
  }
}

TEST(SdfPulseLimitAnnotation, SdfRejectOnlyFullyReplacesPriorPathpulseLimits) {
  PathDelay pd = MakePathWithUniformDelay(40);
  ApplyPulseControlOverride(pd, 9, true, 21);
  ApplySdfPulseLimits(pd, 5, false, 0);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 5u);
    EXPECT_EQ(pd.error_limit[i], 5u);
  }
}

TEST(SdfPulseLimitAnnotation, SdfWinsOverGlobalAndPathpulseCombined) {
  PathDelay pd = MakePathWithUniformDelay(100);
  ApplyGlobalPulseLimits(pd, 20, 80);
  ApplyPulseControlOverride(pd, 3, true, 6);
  ApplySdfPulseLimits(pd, 17, true, 23);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 17u);
    EXPECT_EQ(pd.error_limit[i], 23u);
  }
}

TEST(SdfPulseLimitAnnotation, PathpulseAppliedAfterSdfLeavesTheAnnotation) {
  PathDelay pd = MakePathWithUniformDelay(40);
  ApplySdfPulseLimits(pd, 11, true, 13);
  ApplyPulseControlOverride(pd, 2, true, 7);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 11u);
    EXPECT_EQ(pd.error_limit[i], 13u);
  }
}

TEST(SdfPulseLimitAnnotation, GlobalLimitsAppliedAfterSdfLeaveTheAnnotation) {
  PathDelay pd = MakePathWithUniformDelay(100);
  ApplySdfPulseLimits(pd, 4, true, 8);
  ApplyGlobalPulseLimits(pd, 50, 75);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 4u);
    EXPECT_EQ(pd.error_limit[i], 8u);
  }
}

TEST(SdfPulseLimitAnnotation, GlobalLimitsAppliedAfterPathpulseLeaveIt) {
  PathDelay pd = MakePathWithUniformDelay(100);
  ApplyPulseControlOverride(pd, 3, true, 6);
  ApplyGlobalPulseLimits(pd, 20, 80);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 3u);
    EXPECT_EQ(pd.error_limit[i], 6u);
  }
}

TEST(SdfPulseLimitAnnotation, GlobalLimitsReachAPathNoOtherSourceSet) {
  PathDelay pd = MakePathWithUniformDelay(100);
  ApplyGlobalPulseLimits(pd, 20, 80);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 20u);
    EXPECT_EQ(pd.error_limit[i], 80u);
  }
}

TEST(SdfPulseLimitAnnotation, SdfWinsWhateverOrderTheSourcesArriveIn) {
  PathDelay pd = MakePathWithUniformDelay(100);
  ApplySdfPulseLimits(pd, 17, true, 23);
  ApplyPulseControlOverride(pd, 3, true, 6);
  ApplyGlobalPulseLimits(pd, 20, 80);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd.reject_limit[i], 17u);
    EXPECT_EQ(pd.error_limit[i], 23u);
  }
}

const char* const kOnePathWithPathpulse =
    "module t(input a, output y);\n"
    "  specify\n"
    "    specparam PATHPULSE$a$y = (2, 9);\n"
    "    (a => y) = 20;\n"
    "  endspecify\n"
    "endmodule\n";

void ExpectAyLimits(const SpecifyManager& mgr, uint64_t reject,
                    uint64_t error) {
  const PathDelay* pd = PathWith(mgr, "a", "y", "", false);
  ASSERT_NE(pd, nullptr);
  for (int i = 0; i < 12; ++i) {
    EXPECT_EQ(pd->reject_limit[i], reject) << i;
    EXPECT_EQ(pd->error_limit[i], error) << i;
  }
}

TEST(SdfPulseLimitPrecedence, SdfPathpulseTextOverridesSpecparam) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kOnePathWithPathpulse, f, mgr));
  AnnotateFileOnto(DelaySdf("(PATHPULSE a y (5) (15))"), mgr);
  ExpectAyLimits(mgr, 5, 15);
}

TEST(SdfPulseLimitPrecedence, SdfRejectOnlyTextReplacesBothSpecparamLimits) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kOnePathWithPathpulse, f, mgr));
  AnnotateFileOnto(DelaySdf("(PATHPULSE a y (6))"), mgr);
  ExpectAyLimits(mgr, 6, 6);
}

TEST(SdfPulseLimitPrecedence, SdfPathpulsepercentOverridesSpecparam) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kOnePathWithPathpulse, f, mgr));
  AnnotateFileOnto(DelaySdf("(PATHPULSEPERCENT a y (25) (75))"), mgr);
  ExpectAyLimits(mgr, 5, 15);
}

TEST(SdfPulseLimitPrecedence, SdfOnAnotherPathLeavesThisPathsSpecparam) {
  SimFixture f;
  SpecifyManager mgr;
  ASSERT_TRUE(BuildSpecifyFromSource(kOnePathWithPathpulse, f, mgr));
  AnnotateFileOnto(DelaySdf("(PATHPULSE b z (5) (15))"), mgr);
  ExpectAyLimits(mgr, 2, 9);
}

std::string WriteSdf(const std::string& stem, const std::string& entry) {
  const std::string kPath = "/tmp/delta_c30_07_03_" + stem + ".sdf";
  std::ofstream out(kPath, std::ios::trunc);
  out << "(DELAYFILE (CELL (CELLTYPE \"drive\") (INSTANCE top/c) "
         "(DELAY (ABSOLUTE " +
             entry + "))))\n";
  out.close();
  return kPath;
}

std::string RunAnnotatedPulse(const std::vector<std::string>& args,
                              const std::string& specify_extra,
                              const std::string& sdf_path) {
  SimFixture f;
  CliOptions opts;
  EXPECT_TRUE(ParseCommandLine(args, opts));
  ApplyPulseControlOptions(opts, f.ctx.AcquireSpecifyManager());
  const std::string kAnnotate =
      sdf_path.empty() ? "" : "    $sdf_annotate(\"" + sdf_path + "\");\n";
  return RunCapture(
      "module drive(input a, output y);\n"
      "  assign y = a;\n"
      "  specify\n"
      "    (a => y) = 7;\n" +
          specify_extra +
          "  endspecify\n"
          "endmodule\n"
          "module top;\n"
          "  logic in;\n"
          "  wire out;\n"
          "  drive c(.a(in), .y(out));\n"
          "  always @(out) if ($time > 0) $display(\"t=%0t y=%b\", $time, "
          "out);\n"
          "  initial begin\n" +
          kAnnotate +
          "    in = 1;\n"
          "    #10 in = 0;\n"
          "    #4 in = 1;\n"
          "  end\n"
          "endmodule\n",
      f);
}

std::vector<std::string> HalfPercent() {
  return {"--pulse-reject-limit", "50", "--pulse-error-limit", "50"};
}

TEST(SdfPulseLimitRun, SpecparamRejectsThePulseWithoutAnnotation) {
  EXPECT_EQ(RunAnnotatedPulse(HalfPercent(),
                              "    specparam PATHPULSE$a$y = (5);\n", ""),
            "t=7 y=1\n");
}

TEST(SdfPulseLimitRun, SdfLimitsLetThePulseThroughDespiteSpecparam) {
  EXPECT_EQ(
      RunAnnotatedPulse(HalfPercent(), "    specparam PATHPULSE$a$y = (5);\n",
                        WriteSdf("loose", "(PATHPULSE a y (3))")),
      "t=7 y=1\nt=17 y=0\nt=21 y=1\n");
}

TEST(SdfPulseLimitRun, SdfLimitsRejectThePulseTheOptionsWouldPass) {
  EXPECT_EQ(RunAnnotatedPulse(HalfPercent(), "",
                              WriteSdf("tight", "(PATHPULSE a y (5))")),
            "t=7 y=1\n");
}

TEST(SdfPulseLimitRun, SdfPercentLimitsRejectThePulseTheOptionsWouldPass) {
  EXPECT_EQ(
      RunAnnotatedPulse(HalfPercent(), "",
                        WriteSdf("percent", "(PATHPULSEPERCENT a y (75))")),
      "t=7 y=1\n");
}

TEST(SdfPulseLimitRun, OptionsAloneLetThePulseThrough) {
  EXPECT_EQ(RunAnnotatedPulse(HalfPercent(), "", ""),
            "t=7 y=1\nt=17 y=0\nt=21 y=1\n");
}

TEST(SdfPulseLimitRun, SdfErrorLimitFiltersThePulseToX) {
  EXPECT_EQ(
      RunAnnotatedPulse(HalfPercent(), "    specparam PATHPULSE$a$y = (5);\n",
                        WriteSdf("split", "(PATHPULSE a y (2) (6))")),
      "t=7 y=1\nt=17 y=x\nt=21 y=1\n");
}

}  // namespace
