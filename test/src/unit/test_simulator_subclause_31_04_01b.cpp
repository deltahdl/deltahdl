#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "common/diagnostic.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_timing_check_one_time_step.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

constexpr const char* kDesignBeforeStimulus =
    "module top(\n"
    "    output logic ref_sig,\n"
    "    output logic data_sig);\n"
    "  specify\n"
    "    $skew(posedge ref_sig, posedge data_sig, 46);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    ref_sig = 1'b0;\n"
    "    data_sig = 1'b0;\n";

constexpr const char* kSimultaneousDesignBeforeStimulus =
    "module top(\n"
    "    output logic ref_sig,\n"
    "    output logic data_sig);\n"
    "  specify\n"
    "    $skew(posedge ref_sig, posedge data_sig, 34);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    ref_sig = 1'b0;\n"
    "    data_sig = 1'b0;\n";

bool RanWithStimulus(const char* design, const std::string& stimulus,
                     SimFixture& f) {
  auto* rtl = ElaborateSrc(std::string(design) + stimulus +
                               "  end\n"
                               "endmodule\n",
                           f);
  if (rtl == nullptr || f.has_errors) return false;
  LowerAndRun(rtl, f);
  return true;
}

TEST(DrivenTimingCheckEvaluation, SkewViolationInARunIsReported) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kDesignBeforeStimulus,
                              "    #502 ref_sig = 1'b1;\n"
                              "    #71 data_sig = 1'b1;\n",
                              f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$skew violation: data signal",
      LineHolding(kDesignBeforeStimulus, "$skew(posedge ref_sig"), "31.4.1"));
}

TEST(DrivenTimingCheckEvaluation, SkewSatisfiedInARunReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kDesignBeforeStimulus,
                              "    #530 ref_sig = 1'b1;\n"
                              "    #39 data_sig = 1'b1;\n",
                              f));
  EXPECT_EQ(FindDiag(f, "$skew violation: data signal"), nullptr);
}

TEST(DrivenTimingCheckEvaluation,
     SkewReferenceWithNoDataEventInARunReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus(kDesignBeforeStimulus, "    #566 ref_sig = 1'b1;\n", f));
  EXPECT_EQ(FindDiag(f, "$skew violation: data signal"), nullptr);
}

TEST(DrivenTimingCheckEvaluation,
     SkewSimultaneousEventsWithReferenceAssignedFirstReportNothing) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kSimultaneousDesignBeforeStimulus,
                              "    #620 ref_sig = 1'b1;\n"
                              "    #30 ref_sig = 1'b0;\n"
                              "    #23 ref_sig = 1'b1;\n"
                              "    data_sig = 1'b1;\n",
                              f));
  EXPECT_EQ(FindDiag(f, "$skew violation: data signal"), nullptr);
}

TEST(DrivenTimingCheckEvaluation,
     SkewSimultaneousEventsWithDataAssignedFirstReportNothing) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kSimultaneousDesignBeforeStimulus,
                              "    #620 ref_sig = 1'b1;\n"
                              "    #30 ref_sig = 1'b0;\n"
                              "    #23 data_sig = 1'b1;\n"
                              "    ref_sig = 1'b1;\n",
                              f));
  EXPECT_EQ(FindDiag(f, "$skew violation: data signal"), nullptr);
}

constexpr const char* kSkewViolation = "$skew violation: data signal";

bool RanSkew(const char* limit, const std::string& stimulus, SimFixture& f) {
  std::string src =
      "module top(\n"
      "    output logic r,\n"
      "    output logic d);\n"
      "  specify\n"
      "    $skew(posedge r, posedge d, ";
  src += limit;
  src +=
      ");\n"
      "  endspecify\n"
      "  initial begin\n"
      "    r = 1'b0;\n"
      "    d = 1'b0;\n";
  src += stimulus;
  src +=
      "  end\n"
      "endmodule\n";
  auto* rtl = ElaborateSrc(src, f);
  if (rtl == nullptr || f.has_errors) return false;
  LowerAndRun(rtl, f);
  return true;
}

size_t SkewReports(const SimFixture& f) {
  size_t count = 0;
  for (const Diagnostic& d : f.diag.Diagnostics()) {
    if (d.message.find(kSkewViolation) != std::string::npos) ++count;
  }
  return count;
}

TEST(DrivenTimingCheckEvaluation, SkewDataExactlyAtTheLimitReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(RanSkew("10", "    #5 r = 1'b1;\n    #10 d = 1'b1;\n", f));
  EXPECT_EQ(SkewReports(f), 0u);
}

TEST(DrivenTimingCheckEvaluation, SkewDataOneTickPastTheLimitIsReported) {
  SimFixture f;
  ASSERT_TRUE(RanSkew("10", "    #5 r = 1'b1;\n    #11 d = 1'b1;\n", f));
  EXPECT_TRUE(
      ReportedWarning(f.diag.Diagnostics(), kSkewViolation, 5, "31.4.1"));
}

TEST(DrivenTimingCheckEvaluation, ZeroLimitSkewDataOneTickLaterIsReported) {
  SimFixture f;
  ASSERT_TRUE(RanSkew("0", "    #5 r = 1'b1;\n    #1 d = 1'b1;\n", f));
  EXPECT_TRUE(
      ReportedWarning(f.diag.Diagnostics(), kSkewViolation, 5, "31.4.1"));
}

TEST(DrivenTimingCheckEvaluation, ZeroLimitSkewInOneTimeStepReportsNothing) {
  EXPECT_TRUE(
      SilentInEitherOrder("$skew(posedge r, posedge d, 0);", kSkewViolation));
}

TEST(DrivenTimingCheckEvaluation, SkewJudgesAnArbitrarilyLateDataEvent) {
  SimFixture f;
  ASSERT_TRUE(RanSkew("10", "    #5 r = 1'b1;\n    #100000 d = 1'b1;\n", f));
  EXPECT_EQ(SkewReports(f), 1u);
  EXPECT_TRUE(
      ReportedWarning(f.diag.Diagnostics(), kSkewViolation, 5, "31.4.1"));
}

TEST(DrivenTimingCheckEvaluation, SecondReferenceRestartsTheSkewWait) {
  SimFixture f;
  ASSERT_TRUE(RanSkew("10",
                      "    #5 r = 1'b1;\n"
                      "    #7 r = 1'b0;\n"
                      "    #8 r = 1'b1;\n"
                      "    #5 d = 1'b1;\n",
                      f));
  EXPECT_EQ(SkewReports(f), 0u);
}

TEST(DrivenTimingCheckEvaluation, SkewDataWithoutAReferenceReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(RanSkew("10",
                      "    #5 d = 1'b1;\n"
                      "    #30 d = 1'b0;\n"
                      "    #30 d = 1'b1;\n",
                      f));
  EXPECT_EQ(SkewReports(f), 0u);
}

TEST(DrivenTimingCheckEvaluation,
     SkewReportsEveryLateDataEventAfterOneReference) {
  SimFixture f;
  ASSERT_TRUE(RanSkew("10",
                      "    #5 r = 1'b1;\n"
                      "    #20 d = 1'b1;\n"
                      "    #5 d = 1'b0;\n"
                      "    #5 d = 1'b1;\n",
                      f));
  EXPECT_EQ(SkewReports(f), 2u);
}

}  // namespace
