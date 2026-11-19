#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_timing_check_one_time_step.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

constexpr const char* kDesignThroughTheCheck =
    "module top(\n"
    "    output logic d,\n"
    "    output logic clk);\n"
    "  specify\n"
    "    $setuphold(posedge clk, d, 21, 6);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    d = 1'b0;\n"
    "    clk = 1'b0;\n";

bool RanWithStimulus(const std::string& stimulus, SimFixture& f) {
  auto* rtl = ElaborateSrc(std::string(kDesignThroughTheCheck) + stimulus +
                               "  end\n"
                               "endmodule\n",
                           f);
  if (rtl == nullptr || f.has_errors) return false;
  LowerAndRun(rtl, f);
  return true;
}

TEST(DrivenTimingCheckEvaluation, SetupholdSetupSideViolationInARunIsReported) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #141 d = 1'b1;\n"
                      "    #13 clk = 1'b1;\n",
                      f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$setuphold violation: data signal",
      LineHolding(kDesignThroughTheCheck, "$setuphold(posedge clk"), "31.3.3"));
}

TEST(DrivenTimingCheckEvaluation, SetupholdHoldSideViolationInARunIsReported) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #116 clk = 1'b1;\n"
                      "    #4 d = 1'b1;\n",
                      f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$setuphold violation: data signal",
      LineHolding(kDesignThroughTheCheck, "$setuphold(posedge clk"), "31.3.3"));
}

TEST(DrivenTimingCheckEvaluation, SetupholdSatisfiedInARunReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #128 d = 1'b1;\n"
                      "    #35 clk = 1'b1;\n",
                      f));
  EXPECT_EQ(FindDiag(f, "$setuphold violation: data signal"), nullptr);
}

TEST(DrivenTimingCheckEvaluation,
     SetupholdPositiveLimitsInOneTimeStepViolateInEitherOrder) {
  EXPECT_TRUE(ViolatesInEitherOrder("$setuphold(posedge r, posedge d, 21, 6);",
                                    "$setuphold violation: data signal",
                                    "31.3.3"));
}

TEST(DrivenTimingCheckEvaluation,
     DISABLED_SetupholdZeroHoldInOneTimeStepReportsNothingLikeSetupAndHold) {
  EXPECT_TRUE(SilentInEitherOrder("$setuphold(posedge r, posedge d, 5, 0);",
                                  "$setuphold violation: data signal"));
}

TEST(DrivenTimingCheckEvaluation,
     DISABLED_SetupholdZeroSetupInOneTimeStepViolatesLikeHold) {
  EXPECT_TRUE(ViolatesInEitherOrder("$setuphold(posedge r, posedge d, 0, 5);",
                                    "$setuphold violation: data signal",
                                    "31.3.3"));
}

TEST(DrivenTimingCheckEvaluation,
     SetupholdZeroLimitsInOneTimeStepReportNothing) {
  EXPECT_TRUE(SilentInEitherOrder("$setuphold(posedge r, posedge d, 0, 0);",
                                  "$setuphold violation: data signal"));
}

}  // namespace
