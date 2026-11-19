#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

constexpr const char* kDesignBeforeStimulus =
    "module top(\n"
    "    output logic clk);\n"
    "  specify\n"
    "    $period(posedge clk, 61);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    clk = 1'b0;\n";

bool RanWithStimulus(const std::string& stimulus, SimFixture& f) {
  auto* rtl = ElaborateSrc(std::string(kDesignBeforeStimulus) + stimulus +
                               "  end\n"
                               "endmodule\n",
                           f);
  if (rtl == nullptr || f.has_errors) return false;
  LowerAndRun(rtl, f);
  return true;
}

TEST(DrivenTimingCheckEvaluation, PeriodViolationInARunIsReported) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #902 clk = 1'b1;\n"
                      "    #16 clk = 1'b0;\n"
                      "    #28 clk = 1'b1;\n",
                      f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$period violation: signal",
      LineHolding(kDesignBeforeStimulus, "$period(posedge clk"), "31.4.5"));
}

TEST(DrivenTimingCheckEvaluation, PeriodSatisfiedInARunReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #950 clk = 1'b1;\n"
                      "    #31 clk = 1'b0;\n"
                      "    #47 clk = 1'b1;\n",
                      f));
  EXPECT_EQ(FindDiag(f, "$period violation: signal"), nullptr);
}

constexpr const char* kPeriodViolation = "$period violation: signal";

bool RanPeriod(const char* reference, const char* initial,
               const std::string& stimulus, SimFixture& f) {
  std::string src =
      "module top(\n"
      "    output logic clk);\n"
      "  specify\n"
      "    $period(";
  src += reference;
  src +=
      ", 10);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    clk = ";
  src += initial;
  src += ";\n";
  src += stimulus;
  src +=
      "  end\n"
      "endmodule\n";
  auto* rtl = ElaborateSrc(src, f);
  if (rtl == nullptr || f.has_errors) return false;
  LowerAndRun(rtl, f);
  return true;
}

TEST(DrivenTimingCheckEvaluation,
     PeriodEdgesExactlyTheLimitApartReportNothing) {
  SimFixture f;
  ASSERT_TRUE(RanPeriod("posedge clk", "1'b0",
                        "    #5 clk = 1'b1;\n"
                        "    #5 clk = 1'b0;\n"
                        "    #5 clk = 1'b1;\n",
                        f));
  EXPECT_EQ(FindDiag(f, kPeriodViolation), nullptr);
}

TEST(DrivenTimingCheckEvaluation, PeriodNegedgeCloseFallingEdgesAreReported) {
  SimFixture f;
  ASSERT_TRUE(RanPeriod("negedge clk", "1'b1",
                        "    #5 clk = 1'b0;\n"
                        "    #2 clk = 1'b1;\n"
                        "    #5 clk = 1'b0;\n",
                        f));
  EXPECT_TRUE(
      ReportedWarning(f.diag.Diagnostics(), kPeriodViolation, 4, "31.4.5"));
}

TEST(DrivenTimingCheckEvaluation,
     PeriodNegedgeRisingEdgeBetweenDoesNotRestartTheMeasure) {
  SimFixture f;
  ASSERT_TRUE(RanPeriod("negedge clk", "1'b1",
                        "    #5 clk = 1'b0;\n"
                        "    #4 clk = 1'b1;\n"
                        "    #7 clk = 1'b0;\n",
                        f));
  EXPECT_EQ(FindDiag(f, kPeriodViolation), nullptr);
}

TEST(DrivenTimingCheckEvaluation, PeriodEdgeControlCloseMatchingEdgesReported) {
  SimFixture f;
  ASSERT_TRUE(RanPeriod("edge [01] clk", "1'b0",
                        "    #5 clk = 1'b1;\n"
                        "    #2 clk = 1'b0;\n"
                        "    #5 clk = 1'b1;\n",
                        f));
  EXPECT_TRUE(
      ReportedWarning(f.diag.Diagnostics(), kPeriodViolation, 4, "31.4.5"));
}

TEST(DrivenTimingCheckEvaluation, PeriodEdgeControlIgnoresUnlistedTransitions) {
  SimFixture f;
  ASSERT_TRUE(RanPeriod("edge [01] clk", "1'b0",
                        "    #5 clk = 1'b1;\n"
                        "    #2 clk = 1'b0;\n"
                        "    #2 clk = 1'bx;\n"
                        "    #2 clk = 1'b1;\n"
                        "    #2 clk = 1'b0;\n"
                        "    #7 clk = 1'b1;\n",
                        f));
  EXPECT_EQ(FindDiag(f, kPeriodViolation), nullptr);
}

}  // namespace
