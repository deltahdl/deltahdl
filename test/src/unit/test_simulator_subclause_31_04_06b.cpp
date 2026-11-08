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
    "    output logic ctl,\n"
    "    output logic d);\n"
    "  specify\n"
    "    $nochange(posedge ctl, d, 0, 0);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    ctl = 1'b0;\n"
    "    d = 1'b0;\n";

constexpr const char* kOffsetDesignBeforeStimulus =
    "module top(\n"
    "    output logic ctl,\n"
    "    output logic d);\n"
    "  specify\n"
    "    $nochange(posedge ctl, d, 27, -14);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    ctl = 1'b0;\n"
    "    d = 1'b0;\n";

bool RanWithStimulus(const std::string& design, const std::string& stimulus,
                     SimFixture& f) {
  auto* rtl = ElaborateSrc(design + stimulus +
                               "  end\n"
                               "endmodule\n",
                           f);
  if (rtl == nullptr || f.has_errors) return false;
  LowerAndRun(rtl, f);
  return true;
}

TEST(DrivenTimingCheckEvaluation, NochangeViolationInARunIsReported) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kDesignBeforeStimulus,
                              "    #1204 ctl = 1'b1;\n"
                              "    #12 d = 1'b1;\n"
                              "    #20 ctl = 1'b0;\n",
                              f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$nochange violation: data signal",
      LineHolding(kDesignBeforeStimulus, "$nochange(posedge ctl"), "31.4.6"));
}

TEST(DrivenTimingCheckEvaluation, NochangeSatisfiedInARunReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kDesignBeforeStimulus,
                              "    #1250 ctl = 1'b1;\n"
                              "    #41 ctl = 1'b0;\n"
                              "    #96 d = 1'b1;\n",
                              f));
  EXPECT_EQ(FindDiag(f, "$nochange violation: data signal"), nullptr);
}

TEST(DrivenTimingCheckEvaluation, NochangeOffsetsAreRegisteredAsWritten) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kOffsetDesignBeforeStimulus, "", f));
  const SpecifyManager* mgr = f.ctx.GetSpecifyManager();
  ASSERT_NE(mgr, nullptr);
  ASSERT_EQ(mgr->GetTimingChecks().size(), 1U);
  const TimingCheckEntry& check = mgr->GetTimingChecks()[0];
  EXPECT_EQ(check.start_edge_offset, 27);
  EXPECT_EQ(check.end_edge_offset, -14);
  EXPECT_EQ(check.limit, 0U);
  EXPECT_EQ(check.limit2, 0U);
}

TEST(DrivenTimingCheckEvaluation,
     NochangeStartEdgeOffsetWidensTheWindowIntoAViolation) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kOffsetDesignBeforeStimulus,
                              "    #1327 ctl = 1'b1;\n"
                              "    d = 1'b1;\n"
                              "    #38 ctl = 1'b0;\n",
                              f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$nochange violation: data signal",
      LineHolding(kOffsetDesignBeforeStimulus, "$nochange(posedge ctl"),
      "31.4.6"));
}

TEST(DrivenTimingCheckEvaluation,
     NochangeDataOutsideTheWidenedWindowReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kOffsetDesignBeforeStimulus,
                              "    #1373 ctl = 1'b1;\n"
                              "    #24 ctl = 1'b0;\n"
                              "    #52 d = 1'b1;\n"
                              "    #33 ctl = 1'b1;\n",
                              f));
  EXPECT_EQ(FindDiag(f, "$nochange violation: data signal"), nullptr);
}

TEST(DrivenTimingCheckEvaluation,
     NochangeDataInsideTheStartOffsetIntervalIsReported) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kOffsetDesignBeforeStimulus,
                              "    #1511 d = 1'b1;\n"
                              "    #9 ctl = 1'b1;\n"
                              "    #63 ctl = 1'b0;\n",
                              f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$nochange violation: data signal",
      LineHolding(kOffsetDesignBeforeStimulus, "$nochange(posedge ctl"),
      "31.4.6"));
}

TEST(DrivenTimingCheckEvaluation,
     NochangeDataAtTheWindowBeginningReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kOffsetDesignBeforeStimulus,
                              "    #1604 d = 1'b1;\n"
                              "    #27 ctl = 1'b1;\n"
                              "    #46 ctl = 1'b0;\n",
                              f));
  EXPECT_EQ(FindDiag(f, "$nochange violation: data signal"), nullptr);
}

TEST(DrivenTimingCheckEvaluation,
     NochangeDataBeforeASecondLeadingEdgeIsReportedAgainstThatWindow) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kOffsetDesignBeforeStimulus,
                              "    #1706 ctl = 1'b1;\n"
                              "    #45 ctl = 1'b0;\n"
                              "    #42 d = 1'b1;\n"
                              "    #10 ctl = 1'b1;\n"
                              "    #58 ctl = 1'b0;\n",
                              f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$nochange violation: data signal",
      LineHolding(kOffsetDesignBeforeStimulus, "$nochange(posedge ctl"),
      "31.4.6"));
}

TEST(DrivenTimingCheckEvaluation,
     NochangeDataAtASecondWindowBeginningReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kOffsetDesignBeforeStimulus,
                              "    #1904 ctl = 1'b1;\n"
                              "    #32 ctl = 1'b0;\n"
                              "    #35 d = 1'b1;\n"
                              "    #27 ctl = 1'b1;\n"
                              "    #51 ctl = 1'b0;\n",
                              f));
  EXPECT_EQ(FindDiag(f, "$nochange violation: data signal"), nullptr);
}

TEST(DrivenTimingCheckEvaluation, NochangeTogglesTheNotifierAtEachDataEvent) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top(\n"
                       "    output reg clk = 0,\n"
                       "    output reg d = 0);\n"
                       "  reg n = 0; integer cnt = 0;\n"
                       "  specify\n"
                       "    $nochange(posedge clk, d, 0, 0, n);\n"
                       "  endspecify\n"
                       "  always @(n) cnt = cnt + 1;\n"
                       "  initial begin\n"
                       "    #10 clk = 1;\n"
                       "    #3 d = 1; #1 $display(\"%0d\", cnt);\n"
                       "    #2 d = 0; #1 $display(\"%0d\", cnt);\n"
                       "    #3 clk = 0;\n"
                       "    #5 d = 1; #1 $display(\"%0d\", cnt);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1\n2\n2\n");
}

TEST(DrivenTimingCheckEvaluation,
     NochangeDataChangeBeforeTheTrailingEdgeOfItsTimeStepIsNoViolation) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top(\n"
                       "    output reg clk = 0,\n"
                       "    output reg d = 0);\n"
                       "  reg n = 0; integer cnt = 0;\n"
                       "  specify\n"
                       "    $nochange(posedge clk, d, 0, 0, n);\n"
                       "  endspecify\n"
                       "  always @(n) cnt = cnt + 1;\n"
                       "  initial begin\n"
                       "    #10 clk = 1;\n"
                       "    #10 d = 1; clk = 0;\n"
                       "    #1 $display(\"%0d\", cnt);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "0\n");
  EXPECT_EQ(FindDiag(f, "$nochange violation: data signal"), nullptr);
}

TEST(DrivenTimingCheckEvaluation,
     NochangePositiveEndOffsetTogglesAtTheDataEvent) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top(\n"
                       "    output reg clk = 0,\n"
                       "    output reg d = 0);\n"
                       "  reg n = 0; integer cnt = 0;\n"
                       "  specify\n"
                       "    $nochange(posedge clk, d, 0, 3, n);\n"
                       "  endspecify\n"
                       "  always @(n) cnt = cnt + 1;\n"
                       "  initial begin\n"
                       "    #10 clk = 1; #2 d = 1;\n"
                       "    #1 $display(\"%0d\", cnt);\n"
                       "    #2 clk = 0; #2 d = 0;\n"
                       "    #1 $display(\"%0d\", cnt);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1\n2\n");
}

}  // namespace
