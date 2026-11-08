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

}  // namespace
