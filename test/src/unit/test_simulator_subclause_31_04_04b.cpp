#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"

using namespace delta;

namespace {

constexpr const char* kDesignBeforeStimulus =
    "module top(\n"
    "    output logic clk);\n"
    "  specify\n"
    "    $width(posedge clk, 5, 0);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    clk = 1'b0;\n";

constexpr const char* kThresholdDesignBeforeStimulus =
    "module top(\n"
    "    output logic clk);\n"
    "  specify\n"
    "    $width(posedge clk, 21, 8);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    clk = 1'b0;\n";

constexpr const char* kNoThresholdDesignBeforeStimulus =
    "module top(\n"
    "    output logic clk);\n"
    "  specify\n"
    "    $width(posedge clk, 34);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    clk = 1'b0;\n";

bool RanWithDesignAndStimulus(const char* design, const std::string& stimulus,
                              SimFixture& f) {
  auto* rtl = ElaborateSrc(std::string(design) + stimulus +
                               "  end\n"
                               "endmodule\n",
                           f);
  if (rtl == nullptr || f.has_errors) return false;
  LowerAndRun(rtl, f);
  return true;
}

bool RanWithStimulus(const std::string& stimulus, SimFixture& f) {
  return RanWithDesignAndStimulus(kDesignBeforeStimulus, stimulus, f);
}

const TimingCheckEntry* OnlyRegisteredCheck(SimFixture& f) {
  const SpecifyManager* mgr = f.ctx.GetSpecifyManager();
  if (mgr == nullptr || mgr->GetTimingChecks().size() != 1) return nullptr;
  return &mgr->GetTimingChecks()[0];
}

TEST(DrivenTimingCheckEvaluation, WidthViolationInARunIsReported) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #806 clk = 1'b1;\n"
                      "    #3 clk = 1'b0;\n",
                      f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$width violation: signal",
      LineHolding(kDesignBeforeStimulus, "$width(posedge clk"), "31.4.4"));
}

TEST(DrivenTimingCheckEvaluation, WidthSatisfiedInARunReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus("    #840 clk = 1'b1;\n"
                      "    #7 clk = 1'b0;\n",
                      f));
  EXPECT_EQ(FindDiag(f, "$width violation: signal"), nullptr);
}

TEST(DrivenTimingCheckEvaluation, WidthThresholdReachesTheRegisteredEntry) {
  SimFixture f;
  ASSERT_TRUE(RanWithDesignAndStimulus(kThresholdDesignBeforeStimulus, "", f));
  const TimingCheckEntry* check = OnlyRegisteredCheck(f);
  ASSERT_NE(check, nullptr);
  EXPECT_EQ(check->limit, 21u);
  EXPECT_EQ(check->threshold, 8u);
}

TEST(DrivenTimingCheckEvaluation, WidthGlitchBelowTheThresholdReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(RanWithDesignAndStimulus(kThresholdDesignBeforeStimulus,
                                       "    #902 clk = 1'b1;\n"
                                       "    #6 clk = 1'b0;\n",
                                       f));
  EXPECT_EQ(FindDiag(f, "$width violation: signal"), nullptr);
}

TEST(DrivenTimingCheckEvaluation, WidthPulseAboveTheThresholdIsReported) {
  SimFixture f;
  ASSERT_TRUE(RanWithDesignAndStimulus(kThresholdDesignBeforeStimulus,
                                       "    #934 clk = 1'b1;\n"
                                       "    #13 clk = 1'b0;\n",
                                       f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$width violation: signal",
      LineHolding(kThresholdDesignBeforeStimulus, "$width(posedge clk"),
      "31.4.4"));
}

TEST(DrivenTimingCheckEvaluation, WidthWithoutAThresholdRegistersZero) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithDesignAndStimulus(kNoThresholdDesignBeforeStimulus, "", f));
  const TimingCheckEntry* check = OnlyRegisteredCheck(f);
  ASSERT_NE(check, nullptr);
  EXPECT_EQ(check->limit, 34u);
  EXPECT_EQ(check->threshold, 0u);
  EXPECT_EQ(check->limit2, 0u);
}

}  // namespace
