#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"

using namespace delta;

namespace {

constexpr const char* kDesignBeforeStimulus =
    "module top(\n"
    "    output logic ref_sig,\n"
    "    output logic data_sig);\n"
    "  specify\n"
    "    $timeskew(posedge ref_sig, posedge data_sig, 52);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    ref_sig = 1'b0;\n"
    "    data_sig = 1'b0;\n";

constexpr const char* kSimultaneousDesignBeforeStimulus =
    "module top(\n"
    "    output logic ref_sig,\n"
    "    output logic data_sig);\n"
    "  logic tail_sig;\n"
    "  specify\n"
    "    $timeskew(posedge ref_sig, posedge data_sig, 58);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    ref_sig = 1'b0;\n"
    "    data_sig = 1'b0;\n"
    "    tail_sig = 1'b0;\n";

constexpr const char* kFlagDesignBeforeStimulus =
    "module top(\n"
    "    output logic ref_sig,\n"
    "    output logic data_sig);\n"
    "  specify\n"
    "    $timeskew(posedge ref_sig, posedge data_sig, 66, , 15, 22);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    ref_sig = 1'b0;\n"
    "    data_sig = 1'b0;\n";

constexpr const char* kSuppressedRefDesignBeforeStimulus =
    "module top(\n"
    "    output logic ref_sig,\n"
    "    output logic data_sig);\n"
    "  logic en;\n"
    "  logic tail_sig;\n"
    "  specify\n"
    "    $timeskew(posedge ref_sig &&& en, posedge data_sig, 74, , , 0);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    ref_sig = 1'b0;\n"
    "    data_sig = 1'b0;\n"
    "    en = 1'b1;\n"
    "    tail_sig = 1'b0;\n";

constexpr const char* kRemainActiveDesignBeforeStimulus =
    "module top(\n"
    "    output logic ref_sig,\n"
    "    output logic data_sig);\n"
    "  logic en;\n"
    "  logic tail_sig;\n"
    "  specify\n"
    "    $timeskew(posedge ref_sig &&& en, posedge data_sig, 74, , , 11);\n"
    "  endspecify\n"
    "  initial begin\n"
    "    ref_sig = 1'b0;\n"
    "    data_sig = 1'b0;\n"
    "    en = 1'b1;\n"
    "    tail_sig = 1'b0;\n";

constexpr const char* kEventBasedDesignBeforeStimulus =
    "module top(\n"
    "    output logic ref_sig,\n"
    "    output logic data_sig);\n"
    "  specify\n"
    "    $timeskew(posedge ref_sig, posedge data_sig, 44, , 37);\n"
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

const TimingCheckEntry* OnlyRegisteredCheck(SimFixture& f) {
  const SpecifyManager* mgr = f.ctx.GetSpecifyManager();
  if (mgr == nullptr || mgr->GetTimingChecks().size() != 1) return nullptr;
  return &mgr->GetTimingChecks()[0];
}

TEST(DrivenTimingCheckEvaluation, TimeskewViolationInARunIsReported) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kDesignBeforeStimulus,
                              "    #601 ref_sig = 1'b1;\n"
                              "    #87 data_sig = 1'b1;\n",
                              f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$timeskew violation: data signal",
      LineHolding(kDesignBeforeStimulus, "$timeskew(posedge ref_sig"),
      "31.4.2"));
}

TEST(DrivenTimingCheckEvaluation, TimeskewSatisfiedInARunReportsNothing) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kDesignBeforeStimulus,
                              "    #640 ref_sig = 1'b1;\n"
                              "    #43 data_sig = 1'b1;\n",
                              f));
  EXPECT_EQ(FindDiag(f, "$timeskew violation: data signal"), nullptr);
}

TEST(DrivenTimingCheckEvaluation,
     TimeskewSimultaneousEventsWithReferenceAssignedFirstReportNothing) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kSimultaneousDesignBeforeStimulus,
                              "    #667 ref_sig = 1'b1;\n"
                              "    data_sig = 1'b1;\n"
                              "    #94 tail_sig = 1'b1;\n",
                              f));
  EXPECT_EQ(FindDiag(f, "$timeskew violation: data signal"), nullptr);
}

TEST(DrivenTimingCheckEvaluation,
     TimeskewSimultaneousEventsWithDataAssignedFirstReportNothing) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kSimultaneousDesignBeforeStimulus,
                              "    #667 data_sig = 1'b1;\n"
                              "    ref_sig = 1'b1;\n"
                              "    #94 tail_sig = 1'b1;\n",
                              f));
  EXPECT_EQ(FindDiag(f, "$timeskew violation: data signal"), nullptr);
}

TEST(DrivenTimingCheckEvaluation, TimeskewFlagsAreRegisteredAsWritten) {
  SimFixture flagged;
  ASSERT_TRUE(RanWithStimulus(kFlagDesignBeforeStimulus, "", flagged));
  const TimingCheckEntry* written = OnlyRegisteredCheck(flagged);
  ASSERT_NE(written, nullptr);
  EXPECT_TRUE(written->event_based_flag);
  EXPECT_TRUE(written->remain_active_flag);

  SimFixture bare;
  ASSERT_TRUE(RanWithStimulus(kDesignBeforeStimulus, "", bare));
  const TimingCheckEntry* defaulted = OnlyRegisteredCheck(bare);
  ASSERT_NE(defaulted, nullptr);
  EXPECT_FALSE(defaulted->event_based_flag);
  EXPECT_FALSE(defaulted->remain_active_flag);
}

TEST(DrivenTimingCheckEvaluation,
     TimeskewSuppressedReferenceEventTurnsTheCheckDormant) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kSuppressedRefDesignBeforeStimulus,
                              "    #915 ref_sig = 1'b1;\n"
                              "    #17 ref_sig = 1'b0;\n"
                              "    en = 1'b0;\n"
                              "    #21 ref_sig = 1'b1;\n"
                              "    #79 tail_sig = 1'b1;\n",
                              f));
  EXPECT_EQ(FindDiag(f, "$timeskew violation: data signal"), nullptr);
}

TEST(DrivenTimingCheckEvaluation,
     TimeskewSuppressedReferenceEventWithRemainActiveFlagStillReports) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kRemainActiveDesignBeforeStimulus,
                              "    #915 ref_sig = 1'b1;\n"
                              "    #17 ref_sig = 1'b0;\n"
                              "    en = 1'b0;\n"
                              "    #21 ref_sig = 1'b1;\n"
                              "    #79 tail_sig = 1'b1;\n",
                              f));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "$timeskew violation: data signal",
                              LineHolding(kRemainActiveDesignBeforeStimulus,
                                          "$timeskew(posedge ref_sig"),
                              "31.4.2"));
}

TEST(DrivenTimingCheckEvaluation,
     TimeskewEventBasedFlagReportsOnALateDataEvent) {
  SimFixture f;
  ASSERT_TRUE(RanWithStimulus(kEventBasedDesignBeforeStimulus,
                              "    #968 ref_sig = 1'b1;\n"
                              "    #18 data_sig = 1'b1;\n"
                              "    #14 data_sig = 1'b0;\n"
                              "    #25 data_sig = 1'b1;\n",
                              f));
  EXPECT_TRUE(ReportedWarning(
      f.diag.Diagnostics(), "$timeskew violation: data signal",
      LineHolding(kEventBasedDesignBeforeStimulus, "$timeskew(posedge ref_sig"),
      "31.4.2"));
}

}  // namespace
