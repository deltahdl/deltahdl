#include <gtest/gtest.h>

#include "common/types.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// A negative $setuphold, as in §31.9.1 Example 1: $setuphold(posedge CLK,
// DATA, -10, 20). The negative setup shifts the constraint window off the
// reference edge; the simulator delays CLK and DATA internally so the window
// overlaps the reference again. With signed_limit (setup) = -10 and
// signed_limit2 (hold) = 20 the negative-timing window centered on the
// reference is the open interval (ref + 10, ref + 20): a data transition
// strictly inside it is a violation.
TimingCheckEntry MakeNegativeSetuphold() {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kSetuphold;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.negative_timing_check_enabled = true;
  tc.signed_limit = -10;  // setup
  tc.signed_limit2 = 20;  // hold
  return tc;
}

// §31.9.3: the notifier toggles when the *delayed* reference/data signals, as
// measured by the adjusted limits, are in violation — not when the *undelayed*
// signals at the model inputs would be. This test produces both verdicts from
// real production code (the §31.9.1 negative-window detection reached through
// SpecifyManager::CheckSetupholdViolation) and observes the §31.6 notifier
// (ToggleNotifierOnViolation) follow the delayed-signal verdict.
//
// Here the raw model inputs do NOT violate — the data settles before the
// window — yet the internally delayed data lands inside the shifted window, so
// detection is delayed and the notifier must still toggle.
TEST(NegativeTimingCheckNotifierToggle, TogglesOnDelayedViolationNotRawInput) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeNegativeSetuphold());

  // Undelayed model inputs: data at 105 is outside (110, 120) -> no violation.
  const bool kUndelayed = mgr.CheckSetupholdViolation("clk", 100, "data", 105);
  // Delayed data lands at 115, inside (110, 120) -> the adjusted check
  // violates.
  const bool kDelayed = mgr.CheckSetupholdViolation("clk", 100, "data", 115);

  EXPECT_FALSE(kUndelayed);
  EXPECT_TRUE(kDelayed);

  EXPECT_TRUE(NegativeTimingCheckNotifierShouldToggle(kDelayed, kUndelayed));

  Logic4Word notifier{0, 0};
  if (NegativeTimingCheckNotifierShouldToggle(kDelayed, kUndelayed)) {
    notifier = ToggleNotifierOnViolation(notifier);
  }
  // Toggled off the delayed-signal violation even though the raw inputs did not
  // violate.
  EXPECT_TRUE(notifier.IsOne());
}

// §31.9.3 (reject path): the raw model inputs DO violate the original window,
// but the internally delayed data has moved out of the shifted window, so the
// adjusted check does not detect a violation. The notifier must not toggle —
// the undelayed/original verdict is ignored.
TEST(NegativeTimingCheckNotifierToggle, DoesNotToggleWhenOnlyRawInputViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeNegativeSetuphold());

  // Undelayed data at 115 is inside (110, 120) -> the raw inputs violate.
  const bool kUndelayed = mgr.CheckSetupholdViolation("clk", 100, "data", 115);
  // Delayed data at 125 is outside (110, 120) -> the adjusted check is clean.
  const bool kDelayed = mgr.CheckSetupholdViolation("clk", 100, "data", 125);

  EXPECT_TRUE(kUndelayed);
  EXPECT_FALSE(kDelayed);

  EXPECT_FALSE(NegativeTimingCheckNotifierShouldToggle(kDelayed, kUndelayed));

  Logic4Word notifier{0, 0};
  if (NegativeTimingCheckNotifierShouldToggle(kDelayed, kUndelayed)) {
    notifier = ToggleNotifierOnViolation(notifier);
  }
  // Left untouched: a raw-input-only violation does not toggle the notifier.
  EXPECT_TRUE(notifier.IsZero());
}

// §31.9.3: when both the delayed and the undelayed evaluations detect a
// violation, the notifier still toggles — driven, as always, by the delayed
// verdict.
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

// §31.9 states the negative-value behavior of $recrem is identical to
// $setuphold, so §31.9.3's notifier rule governs $recrem checks as well. This
// is the second admitted input form of the rule: a negative $recrem(-10, 20)
// with recovery = -10 and removal = 20 yields the same negative-timing window
// (ref + 10, ref + 20), but the verdict is produced through the distinct
// production path SpecifyManager::CheckRecremViolation.
TimingCheckEntry MakeNegativeRecrem() {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kRecrem;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.negative_timing_check_enabled = true;
  tc.signed_limit = -10;  // recovery
  tc.signed_limit2 = 20;  // removal
  return tc;
}

// §31.9.3 for $recrem (accept path): the raw model inputs do not violate, but
// the internally delayed data lands inside the window, so the notifier toggles
// off the delayed verdict.
//
// MakeNegativeRecrem writes -10 as the recovery limit and 20 as the removal
// limit, and Table 31-6 gives the removal limit the reference_event role, so
// the removal limit bounds the side before the reference and the recovery limit
// the side after. The window is (100 - 20, 100 + -10), which is (80, 90) and
// lies wholly before the reference. §31.9.1 delays a signal rather than
// advancing it, so the delayed time is the later of the two.
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

// §31.9.3 for $recrem (reject path): only the raw model inputs violate; the
// delayed data has moved out of the window, so the notifier must stay put. The
// window is the (80, 90) the case above states, and the delayed time is again
// the later of the two.
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
