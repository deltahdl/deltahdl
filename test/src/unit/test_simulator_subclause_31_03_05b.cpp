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
    "    $recovery(posedge rst, posedge clk, 22);\n"
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

TEST(DrivenTimingCheckEvaluation, RecoveryViolationInARunIsReported) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #302 rst = 1'b1;\n"
                      "    #10 clk = 1'b1;\n",
                      f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$recovery violation: data signal",
      LineHolding(kDesignThroughTheCheck, "$recovery(posedge rst"), "31.3.5"));
}

TEST(DrivenTimingCheckEvaluation, RecoverySatisfiedInARunReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #345 rst = 1'b1;\n"
                      "    #37 clk = 1'b1;\n",
                      f));
  EXPECT_EQ(FindDiag(f, "$recovery violation: data signal"), nullptr);
}

}  // namespace
