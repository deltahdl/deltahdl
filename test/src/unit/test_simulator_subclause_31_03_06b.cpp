#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

constexpr const char* kDesignThroughTheCheck =
    "module top(\n"
    "    output logic clr,\n"
    "    output logic clk);\n"
    "  specify\n"
    "    $recrem(posedge clr, posedge clk, 24, 14);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    clr = 1'b0;\n"
    "    clk = 1'b0;\n";

constexpr const char* kSimultaneousDesignThroughTheCheck =
    "module top(\n"
    "    output logic clr,\n"
    "    output logic clk);\n"
    "  specify\n"
    "    $recrem(posedge clr, posedge clk, 45, 27);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    clr = 1'b0;\n"
    "    clk = 1'b0;\n";

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

TEST(DrivenTimingCheckEvaluation, RecremRecoverySideViolationInARunIsReported) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kDesignThroughTheCheck,
                              "    #404 clr = 1'b1;\n"
                              "    #19 clk = 1'b1;\n",
                              f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$recrem violation: data signal",
      LineHolding(kDesignThroughTheCheck, "$recrem(posedge clr"), "31.3.6"));
}

TEST(DrivenTimingCheckEvaluation, RecremRemovalSideViolationInARunIsReported) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kDesignThroughTheCheck,
                              "    #436 clk = 1'b1;\n"
                              "    #2 clr = 1'b1;\n",
                              f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$recrem violation: data signal",
      LineHolding(kDesignThroughTheCheck, "$recrem(posedge clr"), "31.3.6"));
}

TEST(DrivenTimingCheckEvaluation, RecremSatisfiedInARunReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kDesignThroughTheCheck,
                              "    #450 clr = 1'b1;\n"
                              "    #38 clk = 1'b1;\n",
                              f));
  EXPECT_EQ(FindDiag(f, "$recrem violation: data signal"), nullptr);
}

TEST(DrivenTimingCheckEvaluation,
     RecremSimultaneousEventsWithReferenceAssignedFirstAreReported) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kSimultaneousDesignThroughTheCheck,
                              "    #466 clr = 1'b1;\n"
                              "    clk = 1'b1;\n",
                              f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$recrem violation: data signal",
      LineHolding(kSimultaneousDesignThroughTheCheck, "$recrem(posedge clr"),
      "31.3.6"));
}

TEST(DrivenTimingCheckEvaluation,
     RecremSimultaneousEventsWithDataAssignedFirstAreReported) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kSimultaneousDesignThroughTheCheck,
                              "    #466 clk = 1'b1;\n"
                              "    clr = 1'b1;\n",
                              f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$recrem violation: data signal",
      LineHolding(kSimultaneousDesignThroughTheCheck, "$recrem(posedge clr"),
      "31.3.6"));
}

}  // namespace
