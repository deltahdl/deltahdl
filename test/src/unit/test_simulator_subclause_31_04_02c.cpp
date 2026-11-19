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

constexpr const char* kTimeskewViolation = "$timeskew violation: data signal";

bool RanTimeskew(const char* args, const std::string& stimulus, SimFixture& f) {
  std::string src =
      "module top(\n"
      "    output logic r,\n"
      "    output logic d);\n"
      "  logic en;\n"
      "  specify\n"
      "    $timeskew(";
  src += args;
  src +=
      ");\n"
      "  endspecify\n"
      "  initial begin\n"
      "    en = 1'b1;\n"
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

size_t TimeskewReports(const SimFixture& f) {
  size_t count = 0;
  for (const Diagnostic& d : f.diag.Diagnostics()) {
    if (d.message.find(kTimeskewViolation) != std::string::npos) ++count;
  }
  return count;
}

TEST(DrivenTimingCheckEvaluation, TimeskewTimeoutLeavesLaterDataUnreported) {
  SimFixture f;
  ASSERT_TRUE(RanTimeskew("posedge r, posedge d, 10",
                          "    #5 r = 1'b1;\n"
                          "    #20 d = 1'b1;\n"
                          "    #5 d = 1'b0;\n"
                          "    #5 d = 1'b1;\n",
                          f));
  EXPECT_EQ(TimeskewReports(f), 1u);
  EXPECT_TRUE(
      ReportedWarning(f.diag.Diagnostics(), kTimeskewViolation, 6, "31.4.2"));
}

TEST(DrivenTimingCheckEvaluation, TimeskewNextReferenceRearmsADormantCheck) {
  SimFixture f;
  ASSERT_TRUE(RanTimeskew("posedge r, posedge d, 10",
                          "    #5 r = 1'b1;\n"
                          "    #3 d = 1'b1;\n"
                          "    #4 r = 1'b0;\n"
                          "    #8 r = 1'b1;\n"
                          "    #20 r = 1'b0;\n",
                          f));
  EXPECT_EQ(TimeskewReports(f), 1u);
}

TEST(DrivenTimingCheckEvaluation, TimeskewDataExactlyAtTheLimitReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(RanTimeskew("posedge r, posedge d, 10",
                          "    #5 r = 1'b1;\n"
                          "    #10 d = 1'b1;\n"
                          "    #30 d = 1'b0;\n",
                          f));
  EXPECT_EQ(TimeskewReports(f), 0u);
}

TEST(DrivenTimingCheckEvaluation,
     ZeroLimitTimeskewInOneTimeStepReportsNothing) {
  EXPECT_TRUE(SilentInEitherOrder("$timeskew(posedge r, posedge d, 0);",
                                  kTimeskewViolation));
}

TEST(DrivenTimingCheckEvaluation,
     TimeskewReferenceAtTheExpiryReportsNothingAndRestarts) {
  SimFixture f;
  ASSERT_TRUE(RanTimeskew("posedge r, posedge d, 10",
                          "    #5 r = 1'b1;\n"
                          "    #5 r = 1'b0;\n"
                          "    #5 r = 1'b1;\n"
                          "    #9 d = 1'b1;\n"
                          "    #30 d = 1'b0;\n",
                          f));
  EXPECT_EQ(TimeskewReports(f), 0u);
}

TEST(DrivenTimingCheckEvaluation,
     TimeskewReferenceOneUnitPastTheExpiryFollowsAReport) {
  SimFixture f;
  ASSERT_TRUE(RanTimeskew("posedge r, posedge d, 10",
                          "    #5 r = 1'b1;\n"
                          "    #5 r = 1'b0;\n"
                          "    #6 r = 1'b1;\n"
                          "    #4 d = 1'b1;\n"
                          "    #30 d = 1'b0;\n",
                          f));
  EXPECT_EQ(TimeskewReports(f), 1u);
}

TEST(DrivenTimingCheckEvaluation,
     TimeskewEventFlagAloneIsDormantAfterTheFirstViolation) {
  SimFixture f;
  ASSERT_TRUE(RanTimeskew("posedge r, posedge d, 10, , 1",
                          "    #5 r = 1'b1;\n"
                          "    #15 d = 1'b1;\n"
                          "    #5 d = 1'b0;\n"
                          "    #5 d = 1'b1;\n",
                          f));
  EXPECT_EQ(TimeskewReports(f), 1u);
}

TEST(DrivenTimingCheckEvaluation, TimeskewBothFlagsReportEveryLateDataEvent) {
  SimFixture f;
  ASSERT_TRUE(RanTimeskew("posedge r, posedge d, 10, , 1, 1",
                          "    #5 r = 1'b1;\n"
                          "    #30 d = 1'b1;\n"
                          "    #5 d = 1'b0;\n"
                          "    #5 d = 1'b1;\n",
                          f));
  EXPECT_EQ(TimeskewReports(f), 2u);
}

TEST(DrivenTimingCheckEvaluation, TimeskewBothFlagsReportNothingWithoutData) {
  SimFixture f;
  ASSERT_TRUE(RanTimeskew("posedge r, posedge d, 10, , 1, 1",
                          "    #5 r = 1'b1;\n"
                          "    #40 r = 1'b0;\n",
                          f));
  EXPECT_EQ(TimeskewReports(f), 0u);
}

TEST(DrivenTimingCheckEvaluation,
     TimeskewTrueConditionedReferenceRearmsAfterAFalseOne) {
  SimFixture f;
  ASSERT_TRUE(RanTimeskew("posedge r &&& en, posedge d, 10",
                          "    #5 r = 1'b1;\n"
                          "    #3 r = 1'b0;\n"
                          "    en = 1'b0;\n"
                          "    #2 r = 1'b1;\n"
                          "    #2 r = 1'b0;\n"
                          "    en = 1'b1;\n"
                          "    #2 r = 1'b1;\n"
                          "    #20 r = 1'b0;\n",
                          f));
  EXPECT_EQ(TimeskewReports(f), 1u);
}

TEST(DrivenTimingCheckEvaluation,
     TimeskewEventFlagAloneFalseConditionedReferenceLeavesItDormant) {
  SimFixture f;
  ASSERT_TRUE(RanTimeskew("posedge r &&& en, posedge d, 10, , 1, 0",
                          "    #5 r = 1'b1;\n"
                          "    #3 r = 1'b0;\n"
                          "    en = 1'b0;\n"
                          "    #2 r = 1'b1;\n"
                          "    #20 d = 1'b1;\n",
                          f));
  EXPECT_EQ(TimeskewReports(f), 0u);
}

TEST(DrivenTimingCheckEvaluation,
     TimeskewBothFlagsFalseConditionedReferenceLeavesItActive) {
  SimFixture f;
  ASSERT_TRUE(RanTimeskew("posedge r &&& en, posedge d, 10, , 1, 1",
                          "    #5 r = 1'b1;\n"
                          "    #3 r = 1'b0;\n"
                          "    en = 1'b0;\n"
                          "    #2 r = 1'b1;\n"
                          "    #20 d = 1'b1;\n"
                          "    #5 d = 1'b0;\n"
                          "    #5 d = 1'b1;\n",
                          f));
  EXPECT_EQ(TimeskewReports(f), 2u);
}

}  // namespace
