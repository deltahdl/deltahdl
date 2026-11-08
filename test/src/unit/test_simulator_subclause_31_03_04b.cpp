#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

constexpr const char* kDesignThroughTheCheck =
    "module top(\n"
    "    output logic rst,\n"
    "    output logic clk);\n"
    "  specify\n"
    "    $removal(posedge rst, posedge clk, 18);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    rst = 1'b0;\n"
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

TEST(DrivenTimingCheckEvaluation, RemovalViolationInARunIsReported) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #205 clk = 1'b1;\n"
                      "    #8 rst = 1'b1;\n",
                      f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$removal violation: data signal",
      LineHolding(kDesignThroughTheCheck, "$removal(posedge rst"), "31.3.4"));
}

TEST(DrivenTimingCheckEvaluation, RemovalSatisfiedInARunReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #240 clk = 1'b1;\n"
                      "    #25 rst = 1'b1;\n",
                      f));
  EXPECT_EQ(FindDiag(f, "$removal violation: data signal"), nullptr);
}

}  // namespace
