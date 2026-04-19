#include "simulator/specify.h"

#include <gtest/gtest.h>

using namespace delta;

namespace {

// §31.9.3: when neither candidate evaluation reports a violation,
// the notifier does not toggle. This anchors the zero-input case so
// the rule cannot accidentally drift into an unconditional toggle.
TEST(NegativeTimingCheckNotifierToggle, NoViolationDoesNotToggle) {
  EXPECT_FALSE(NegativeTimingCheckNotifierShouldToggle(
      /*delayed_adjusted_violation=*/false,
      /*undelayed_original_violation=*/false));
}

// §31.9.3: a violation detected against the delayed signals using
// the adjusted limits is the sole trigger the LRM allows, so the
// helper toggles when the delayed evaluation fires — regardless of
// what the undelayed evaluation reports.
TEST(NegativeTimingCheckNotifierToggle, DelayedViolationToggles) {
  EXPECT_TRUE(NegativeTimingCheckNotifierShouldToggle(
      /*delayed_adjusted_violation=*/true,
      /*undelayed_original_violation=*/false));
}

// §31.9.3: this is the rule's operative half — the undelayed
// evaluation against the original limits shall never drive the
// notifier. A violation that surfaces only in the undelayed path
// must not cause a toggle.
TEST(NegativeTimingCheckNotifierToggle, UndelayedViolationDoesNotToggle) {
  EXPECT_FALSE(NegativeTimingCheckNotifierShouldToggle(
      /*delayed_adjusted_violation=*/false,
      /*undelayed_original_violation=*/true));
}

// §31.9.3: when both evaluations agree on a violation, the
// delayed-signal evaluation still carries the decision. The
// undelayed argument is irrelevant to the outcome even when it
// happens to match.
TEST(NegativeTimingCheckNotifierToggle, BothViolationsToggle) {
  EXPECT_TRUE(NegativeTimingCheckNotifierShouldToggle(
      /*delayed_adjusted_violation=*/true,
      /*undelayed_original_violation=*/true));
}

}  // namespace
