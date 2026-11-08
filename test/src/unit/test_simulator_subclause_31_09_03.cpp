#include <gtest/gtest.h>

#include "common/types.h"
#include "parser/ast_specify.h"
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

}  // namespace
