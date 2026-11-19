#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "common/diagnostic.h"
#include "fixture_simulator.h"
#include "helpers_timing_check_one_time_step.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

constexpr const char* kFullskewViolation = "$fullskew violation: signals";

bool RanFullskew(const char* args, const std::string& stimulus, SimFixture& f) {
  std::string src =
      "module top(\n"
      "    output logic r,\n"
      "    output logic d);\n"
      "  logic en;\n"
      "  specify\n"
      "    $fullskew(";
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

size_t FullskewReports(const SimFixture& f) {
  size_t count = 0;
  for (const Diagnostic& d : f.diag.Diagnostics()) {
    if (d.message.find(kFullskewViolation) != std::string::npos) ++count;
  }
  return count;
}

TEST(DrivenTimingCheckEvaluation,
     ZeroLimitFullskewInOneTimeStepReportsNothing) {
  EXPECT_TRUE(SilentInEitherOrder("$fullskew(posedge r, posedge d, 0, 0);",
                                  kFullskewViolation));
}

TEST(DrivenTimingCheckEvaluation,
     FullskewReferenceAtTheLimit1ExpiryReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(RanFullskew("posedge r, posedge d, 10, 20",
                          "    #5 r = 1'b1;\n"
                          "    #5 r = 1'b0;\n"
                          "    #5 r = 1'b1;\n"
                          "    #5 d = 1'b1;\n"
                          "    #40 d = 1'b0;\n",
                          f));
  EXPECT_EQ(FullskewReports(f), 0u);
}

TEST(DrivenTimingCheckEvaluation, FullskewDataAtTheLimit2ExpiryReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(RanFullskew("posedge r, posedge d, 10, 20",
                          "    #5 d = 1'b1;\n"
                          "    #10 d = 1'b0;\n"
                          "    #10 d = 1'b1;\n"
                          "    #5 r = 1'b1;\n"
                          "    #40 r = 1'b0;\n",
                          f));
  EXPECT_EQ(FullskewReports(f), 0u);
}

TEST(DrivenTimingCheckEvaluation,
     FullskewReferenceLeadingByExactlyLimit1ReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(RanFullskew("posedge r, posedge d, 10, 20",
                          "    #5 r = 1'b1;\n"
                          "    #10 d = 1'b1;\n"
                          "    #40 d = 1'b0;\n",
                          f));
  EXPECT_EQ(FullskewReports(f), 0u);
}

TEST(DrivenTimingCheckEvaluation,
     FullskewDataLeadingBeyondLimit1WithinLimit2ReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(RanFullskew("posedge r, posedge d, 10, 20",
                          "    #5 d = 1'b1;\n"
                          "    #15 r = 1'b1;\n"
                          "    #40 r = 1'b0;\n",
                          f));
  EXPECT_EQ(FullskewReports(f), 0u);
}

TEST(DrivenTimingCheckEvaluation,
     FullskewDataLeadingByExactlyLimit2ReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(RanFullskew("posedge r, posedge d, 10, 20",
                          "    #5 d = 1'b1;\n"
                          "    #20 r = 1'b1;\n"
                          "    #40 r = 1'b0;\n",
                          f));
  EXPECT_EQ(FullskewReports(f), 0u);
}

TEST(DrivenTimingCheckEvaluation,
     FullskewEventAfterATimeoutOpensAWindowWithItsOwnLimit) {
  SimFixture f;
  ASSERT_TRUE(RanFullskew("posedge r, posedge d, 10, 20",
                          "    #5 r = 1'b1;\n"
                          "    #10 r = 1'b0;\n"
                          "    #15 d = 1'b1;\n"
                          "    #15 r = 1'b1;\n"
                          "    #40 d = 1'b0;\n",
                          f));
  EXPECT_EQ(FullskewReports(f), 1u);
}

TEST(DrivenTimingCheckEvaluation,
     EventBasedFullskewReportsNothingWhenTheLimitElapses) {
  SimFixture f;
  ASSERT_TRUE(RanFullskew("posedge r, posedge d, 10, 20, , 1",
                          "    #5 r = 1'b1;\n"
                          "    #50 r = 1'b0;\n",
                          f));
  EXPECT_EQ(FullskewReports(f), 0u);
}

TEST(DrivenTimingCheckEvaluation,
     TimerFullskewTrueConditionedEventWakesADormantCheck) {
  SimFixture f;
  ASSERT_TRUE(RanFullskew("posedge r &&& en, posedge d, 10, 20",
                          "    #5 r = 1'b1;\n"
                          "    #2 r = 1'b0;\n"
                          "    en = 1'b0;\n"
                          "    #2 r = 1'b1;\n"
                          "    #2 r = 1'b0;\n"
                          "    en = 1'b1;\n"
                          "    #2 r = 1'b1;\n"
                          "    #40 r = 1'b0;\n",
                          f));
  EXPECT_EQ(FullskewReports(f), 1u);
}

TEST(DrivenTimingCheckEvaluation,
     EventBasedFullskewTrueConditionedEventWakesADormantCheck) {
  SimFixture f;
  ASSERT_TRUE(RanFullskew("posedge r &&& en, posedge d, 10, 20, , 1, 0",
                          "    #5 r = 1'b1;\n"
                          "    #2 r = 1'b0;\n"
                          "    en = 1'b0;\n"
                          "    #2 r = 1'b1;\n"
                          "    #2 r = 1'b0;\n"
                          "    en = 1'b1;\n"
                          "    #2 r = 1'b1;\n"
                          "    #17 d = 1'b1;\n"
                          "    #40 d = 1'b0;\n",
                          f));
  EXPECT_EQ(FullskewReports(f), 1u);
}

TEST(DrivenTimingCheckEvaluation,
     TimerFullskewSecondTimestampReplacesTheWindow) {
  SimFixture f;
  ASSERT_TRUE(RanFullskew("posedge r, posedge d, 10, 20",
                          "    #5 r = 1'b1;\n"
                          "    #3 r = 1'b0;\n"
                          "    #4 r = 1'b1;\n"
                          "    #8 d = 1'b1;\n"
                          "    #40 d = 1'b0;\n",
                          f));
  EXPECT_EQ(FullskewReports(f), 0u);
}

TEST(DrivenTimingCheckEvaluation,
     TimerFullskewFalseConditionedSecondReferenceIgnoredWithRemainActive) {
  SimFixture f;
  ASSERT_TRUE(RanFullskew("posedge r &&& en, posedge d, 10, 20, , 0, 1",
                          "    #5 r = 1'b1;\n"
                          "    #2 r = 1'b0;\n"
                          "    en = 1'b0;\n"
                          "    #2 r = 1'b1;\n"
                          "    #40 r = 1'b0;\n",
                          f));
  EXPECT_EQ(FullskewReports(f), 1u);
}

TEST(DrivenTimingCheckEvaluation,
     TimerFullskewFalseConditionedSecondReferenceTurnsItDormant) {
  SimFixture f;
  ASSERT_TRUE(RanFullskew("posedge r &&& en, posedge d, 10, 20, , 0, 0",
                          "    #5 r = 1'b1;\n"
                          "    #2 r = 1'b0;\n"
                          "    en = 1'b0;\n"
                          "    #2 r = 1'b1;\n"
                          "    #40 r = 1'b0;\n",
                          f));
  EXPECT_EQ(FullskewReports(f), 0u);
}

TEST(DrivenTimingCheckEvaluation,
     EventBasedFullskewSecondTimestampReplacesTheWindow) {
  SimFixture f;
  ASSERT_TRUE(RanFullskew("posedge r, posedge d, 10, 20, , 1",
                          "    #5 r = 1'b1;\n"
                          "    #3 r = 1'b0;\n"
                          "    #4 r = 1'b1;\n"
                          "    #9 d = 1'b1;\n"
                          "    #40 d = 1'b0;\n",
                          f));
  EXPECT_EQ(FullskewReports(f), 0u);
}

TEST(DrivenTimingCheckEvaluation,
     EventBasedFullskewFalseConditionedSecondReferenceIgnoredWithRemainActive) {
  SimFixture f;
  ASSERT_TRUE(RanFullskew("posedge r &&& en, posedge d, 10, 20, , 1, 1",
                          "    #5 r = 1'b1;\n"
                          "    #2 r = 1'b0;\n"
                          "    en = 1'b0;\n"
                          "    #2 r = 1'b1;\n"
                          "    #11 d = 1'b1;\n"
                          "    #40 d = 1'b0;\n",
                          f));
  EXPECT_EQ(FullskewReports(f), 1u);
}

TEST(DrivenTimingCheckEvaluation,
     EventBasedFullskewFalseConditionedSecondReferenceTurnsItDormant) {
  SimFixture f;
  ASSERT_TRUE(RanFullskew("posedge r &&& en, posedge d, 10, 20, , 1, 0",
                          "    #5 r = 1'b1;\n"
                          "    #2 r = 1'b0;\n"
                          "    en = 1'b0;\n"
                          "    #2 r = 1'b1;\n"
                          "    #11 d = 1'b1;\n"
                          "    #40 d = 1'b0;\n",
                          f));
  EXPECT_EQ(FullskewReports(f), 0u);
}

}  // namespace
