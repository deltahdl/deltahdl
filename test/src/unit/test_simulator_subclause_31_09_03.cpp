#include <gtest/gtest.h>

#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"
#include "parser/ast_specify.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"

using namespace delta;

namespace {

TimingCheckEntry MakeNegativeSetuphold() {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kSetuphold;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.negative_timing_check_enabled = true;
  tc.signed_limit = -10;
  tc.signed_limit2 = 20;
  return tc;
}

TEST(NegativeTimingCheckNotifierToggle, TogglesOnDelayedViolationNotRawInput) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeNegativeSetuphold());

  const bool kUndelayed = mgr.CheckSetupholdViolation("clk", 100, "data", 105);
  const bool kDelayed = mgr.CheckSetupholdViolation("clk", 100, "data", 115);

  EXPECT_FALSE(kUndelayed);
  EXPECT_TRUE(kDelayed);

  EXPECT_TRUE(NegativeTimingCheckNotifierShouldToggle(kDelayed, kUndelayed));

  Logic4Word notifier{0, 0};
  if (NegativeTimingCheckNotifierShouldToggle(kDelayed, kUndelayed)) {
    notifier = ToggleNotifierOnViolation(notifier);
  }
  EXPECT_TRUE(notifier.IsOne());
}

TEST(NegativeTimingCheckNotifierToggle, DoesNotToggleWhenOnlyRawInputViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeNegativeSetuphold());

  const bool kUndelayed = mgr.CheckSetupholdViolation("clk", 100, "data", 115);
  const bool kDelayed = mgr.CheckSetupholdViolation("clk", 100, "data", 125);

  EXPECT_TRUE(kUndelayed);
  EXPECT_FALSE(kDelayed);

  EXPECT_FALSE(NegativeTimingCheckNotifierShouldToggle(kDelayed, kUndelayed));

  Logic4Word notifier{0, 0};
  if (NegativeTimingCheckNotifierShouldToggle(kDelayed, kUndelayed)) {
    notifier = ToggleNotifierOnViolation(notifier);
  }
  EXPECT_TRUE(notifier.IsZero());
}

TEST(NegativeTimingCheckNotifierToggle, TogglesWhenBothViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeNegativeSetuphold());

  const bool kUndelayed = mgr.CheckSetupholdViolation("clk", 100, "data", 113);
  const bool kDelayed = mgr.CheckSetupholdViolation("clk", 100, "data", 117);

  EXPECT_TRUE(kUndelayed);
  EXPECT_TRUE(kDelayed);

  EXPECT_TRUE(NegativeTimingCheckNotifierShouldToggle(kDelayed, kUndelayed));

  Logic4Word notifier{0, 0};
  notifier = ToggleNotifierOnViolation(notifier);
  EXPECT_TRUE(notifier.IsOne());
}

TimingCheckEntry MakeNegativeRecrem() {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kRecrem;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.negative_timing_check_enabled = true;
  tc.signed_limit = -10;
  tc.signed_limit2 = 20;
  return tc;
}

TEST(NegativeTimingCheckNotifierToggle, RecremTogglesOnDelayedViolation) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeNegativeRecrem());

  const bool kUndelayed = mgr.CheckRecremViolation("clk", 100, "data", 75);
  const bool kDelayed = mgr.CheckRecremViolation("clk", 100, "data", 85);

  EXPECT_FALSE(kUndelayed);
  EXPECT_TRUE(kDelayed);

  EXPECT_TRUE(NegativeTimingCheckNotifierShouldToggle(kDelayed, kUndelayed));

  Logic4Word notifier{0, 0};
  if (NegativeTimingCheckNotifierShouldToggle(kDelayed, kUndelayed)) {
    notifier = ToggleNotifierOnViolation(notifier);
  }
  EXPECT_TRUE(notifier.IsOne());
}

TEST(NegativeTimingCheckNotifierToggle, RecremDoesNotToggleOnRawInputOnly) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeNegativeRecrem());

  const bool kUndelayed = mgr.CheckRecremViolation("clk", 100, "data", 85);
  const bool kDelayed = mgr.CheckRecremViolation("clk", 100, "data", 95);

  EXPECT_TRUE(kUndelayed);
  EXPECT_FALSE(kDelayed);

  EXPECT_FALSE(NegativeTimingCheckNotifierShouldToggle(kDelayed, kUndelayed));

  Logic4Word notifier{0, 0};
  if (NegativeTimingCheckNotifierShouldToggle(kDelayed, kUndelayed)) {
    notifier = ToggleNotifierOnViolation(notifier);
  }
  EXPECT_TRUE(notifier.IsZero());
}

std::string NotifierRun(const std::string& checks,
                        const std::string& stimulus) {
  SimFixture f;
  f.ctx.AcquireSpecifyManager().SetTimingCheckInvocationOptions({true, false});
  return PreprocessAndCapture(
      "`timescale 1ns/1ns\n"
      "module top(output reg clk = 0, output reg d = 0, output reg e = 0);\n"
      "  reg n = 0;\n"
      "  specify\n"
      "    " +
          checks +
          "\n"
          "  endspecify\n"
          "  always @(n) $display(\"toggle %0t\", $time);\n"
          "  initial begin\n"
          "    " +
          stimulus +
          "\n"
          "    #50 $display(\"n %b\", n);\n"
          "  end\n"
          "endmodule\n",
      f);
}

TEST(NegativeTimingCheckNotifierRun, InputsOutsideTheShiftedWindowLeaveIt) {
  EXPECT_EQ(NotifierRun("$setuphold(posedge clk, d, -10, 20, n);",
                        "#100 clk = 1; #5 d = 1;"),
            "n 0\n");
}

TEST(NegativeTimingCheckNotifierRun, InputsInsideTheShiftedWindowToggleIt) {
  EXPECT_EQ(NotifierRun("$setuphold(posedge clk, d, -10, 20, n);",
                        "#100 clk = 1; #15 d = 1;"),
            "toggle 115\nn 1\n");
}

TEST(NegativeTimingCheckNotifierRun, RecremTogglesAtTheDelayedReference) {
  EXPECT_EQ(NotifierRun("$recrem(posedge clk, d, 20, -10); "
                        "$recrem(posedge clk, e, 8, -4, n);",
                        "#100 clk = 1; #5 e = 1;"),
            "toggle 111\nn 1\n");
}

}  // namespace
