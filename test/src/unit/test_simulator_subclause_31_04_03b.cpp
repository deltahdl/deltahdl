#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

constexpr const char* kDesignBeforeStimulus =
    "module top(\n"
    "    output logic ref_sig,\n"
    "    output logic data_sig);\n"
    "  specify\n"
    "    $fullskew(posedge ref_sig, posedge data_sig, 29, 64);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    ref_sig = 1'b0;\n"
    "    data_sig = 1'b0;\n";

constexpr const char* kSimultaneousDesignBeforeStimulus =
    "module top(\n"
    "    output logic ref_sig,\n"
    "    output logic data_sig);\n"
    "  specify\n"
    "    $fullskew(posedge ref_sig, posedge data_sig, 58, 83);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    ref_sig = 1'b0;\n"
    "    data_sig = 1'b0;\n";

constexpr const char* kSuppressedRefDesignBeforeStimulus =
    "module top(\n"
    "    output logic ref_sig,\n"
    "    output logic data_sig);\n"
    "  logic en;\n"
    "  specify\n"
    "    $fullskew(posedge ref_sig &&& en, posedge data_sig, 31, 47);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    ref_sig = 1'b0;\n"
    "    data_sig = 1'b0;\n"
    "    en = 1'b0;\n";

constexpr const char* kRemainActiveDesignBeforeStimulus =
    "module top(\n"
    "    output logic ref_sig,\n"
    "    output logic data_sig);\n"
    "  logic en;\n"
    "  specify\n"
    "    $fullskew(posedge ref_sig &&& en, posedge data_sig, 31, 47, , , 1);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    ref_sig = 1'b0;\n"
    "    data_sig = 1'b0;\n"
    "    en = 1'b0;\n";

constexpr const char* kSuppressedRefStimulus =
    "    #214 data_sig = 1'b1;\n"
    "    #41 ref_sig = 1'b1;\n"
    "    #62;\n";

constexpr const char* kEventBasedDesignBeforeStimulus =
    "module top(\n"
    "    output logic ref_sig,\n"
    "    output logic data_sig);\n"
    "  specify\n"
    "    $fullskew(posedge ref_sig, posedge data_sig, 73, 96, , 1);\n"
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

TEST(DrivenTimingCheckEvaluation, FullskewViolationInARunIsReported) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kDesignBeforeStimulus,
                              "    #703 ref_sig = 1'b1;\n"
                              "    #49 data_sig = 1'b1;\n",
                              f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$fullskew violation: signals",
      LineHolding(kDesignBeforeStimulus, "$fullskew(posedge ref_sig"),
      "31.4.3"));
}

TEST(DrivenTimingCheckEvaluation, FullskewSatisfiedInARunReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kDesignBeforeStimulus,
                              "    #740 ref_sig = 1'b1;\n"
                              "    #26 data_sig = 1'b1;\n",
                              f));
  EXPECT_EQ(FindDiag(f, "$fullskew violation: signals"), nullptr);
}

TEST(DrivenTimingCheckEvaluation,
     FullskewSimultaneousEventsWithReferenceAssignedFirstReportNothing) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kSimultaneousDesignBeforeStimulus,
                              "    #778 ref_sig = 1'b1;\n"
                              "    data_sig = 1'b1;\n"
                              "    #91;\n",
                              f));
  EXPECT_EQ(FindDiag(f, "$fullskew violation: signals"), nullptr);
}

TEST(DrivenTimingCheckEvaluation,
     FullskewSimultaneousEventsWithDataAssignedFirstReportNothing) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kSimultaneousDesignBeforeStimulus,
                              "    #778 data_sig = 1'b1;\n"
                              "    ref_sig = 1'b1;\n"
                              "    #91;\n",
                              f));
  EXPECT_EQ(FindDiag(f, "$fullskew violation: signals"), nullptr);
}

TEST(DrivenTimingCheckEvaluation,
     FullskewSuppressedRefEventWithoutRemainActiveFlagTurnsCheckDormant) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kSuppressedRefDesignBeforeStimulus,
                              kSuppressedRefStimulus, f));
  EXPECT_EQ(FindDiag(f, "$fullskew violation: signals"), nullptr);
}

TEST(DrivenTimingCheckEvaluation,
     FullskewSuppressedRefEventWithRemainActiveFlagLeavesTimerStanding) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kRemainActiveDesignBeforeStimulus,
                              kSuppressedRefStimulus, f));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "$fullskew violation: signals",
                              LineHolding(kRemainActiveDesignBeforeStimulus,
                                          "$fullskew(posedge ref_sig &&& en"),
                              "31.4.3"));
}

TEST(DrivenTimingCheckEvaluation,
     FullskewEventBasedTimecheckBeyondLimitIsReported) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kEventBasedDesignBeforeStimulus,
                              "    #412 ref_sig = 1'b1;\n"
                              "    #88 data_sig = 1'b1;\n"
                              "    #44;\n",
                              f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$fullskew violation: signals",
      LineHolding(kEventBasedDesignBeforeStimulus, "$fullskew(posedge ref_sig"),
      "31.4.3"));
}

TEST(DrivenTimingCheckEvaluation,
     FullskewEventBasedTimecheckWithinLimitReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kEventBasedDesignBeforeStimulus,
                              "    #412 ref_sig = 1'b1;\n"
                              "    #55 data_sig = 1'b1;\n"
                              "    #44;\n",
                              f));
  EXPECT_EQ(FindDiag(f, "$fullskew violation: signals"), nullptr);
}

TEST(DrivenTimingCheckEvaluation,
     FullskewEventBasedTimecheckBecomesTimestampOfANewWindow) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kEventBasedDesignBeforeStimulus,
                              "    #130 ref_sig = 1'b1;\n"
                              "    #79 data_sig = 1'b1;\n"
                              "    #12 ref_sig = 1'b0;\n"
                              "    #106 ref_sig = 1'b1;\n"
                              "    #37;\n",
                              f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$fullskew violation: signals",
      LineHolding(kEventBasedDesignBeforeStimulus, "$fullskew(posedge ref_sig"),
      "31.4.3"));
  std::size_t first = PositionOfFirstDiag(f, "$fullskew violation: signals");
  EXPECT_NE(FindDiagFrom(f, first + 1, "$fullskew violation: signals"),
            nullptr);
}

}  // namespace
