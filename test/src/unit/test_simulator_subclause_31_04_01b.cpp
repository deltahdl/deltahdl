#include <gtest/gtest.h>

#include <string>

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
    "    $skew(posedge ref_sig, posedge data_sig, 46);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    ref_sig = 1'b0;\n"
    "    data_sig = 1'b0;\n";

constexpr const char* kSimultaneousDesignBeforeStimulus =
    "module top(\n"
    "    output logic ref_sig,\n"
    "    output logic data_sig);\n"
    "  specify\n"
    "    $skew(posedge ref_sig, posedge data_sig, 34);\n"
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

TEST(DrivenTimingCheckEvaluation, SkewViolationInARunIsReported) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kDesignBeforeStimulus,
                              "    #502 ref_sig = 1'b1;\n"
                              "    #71 data_sig = 1'b1;\n",
                              f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$skew violation: data signal",
      LineHolding(kDesignBeforeStimulus, "$skew(posedge ref_sig"), "31.4.1"));
}

TEST(DrivenTimingCheckEvaluation, SkewSatisfiedInARunReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kDesignBeforeStimulus,
                              "    #530 ref_sig = 1'b1;\n"
                              "    #39 data_sig = 1'b1;\n",
                              f));
  EXPECT_EQ(FindDiag(f, "$skew violation: data signal"), nullptr);
}

TEST(DrivenTimingCheckEvaluation,
     SkewReferenceWithNoDataEventInARunReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(
      RanWithStimulus(kDesignBeforeStimulus, "    #566 ref_sig = 1'b1;\n", f));
  EXPECT_EQ(FindDiag(f, "$skew violation: data signal"), nullptr);
}

TEST(DrivenTimingCheckEvaluation,
     SkewSimultaneousEventsWithReferenceAssignedFirstReportNothing) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kSimultaneousDesignBeforeStimulus,
                              "    #620 ref_sig = 1'b1;\n"
                              "    #30 ref_sig = 1'b0;\n"
                              "    #23 ref_sig = 1'b1;\n"
                              "    data_sig = 1'b1;\n",
                              f));
  EXPECT_EQ(FindDiag(f, "$skew violation: data signal"), nullptr);
}

TEST(DrivenTimingCheckEvaluation,
     SkewSimultaneousEventsWithDataAssignedFirstReportNothing) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kSimultaneousDesignBeforeStimulus,
                              "    #620 ref_sig = 1'b1;\n"
                              "    #30 ref_sig = 1'b0;\n"
                              "    #23 data_sig = 1'b1;\n"
                              "    ref_sig = 1'b1;\n",
                              f));
  EXPECT_EQ(FindDiag(f, "$skew violation: data signal"), nullptr);
}

}  // namespace
