#include <gtest/gtest.h>

#include "common/types.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

TEST(NotifierUpdate, ZeroTogglesToOne) {
  Logic4Word before{0, 0};
  auto after = ToggleNotifierOnViolation(before);
  EXPECT_TRUE(after.IsOne());
}

TEST(NotifierUpdate, OneTogglesToZero) {
  Logic4Word before{1, 0};
  auto after = ToggleNotifierOnViolation(before);
  EXPECT_TRUE(after.IsZero());
}

TEST(NotifierUpdate, XResolvesToKnownScalar) {
  Logic4Word before{0, 1};
  auto after = ToggleNotifierOnViolation(before);
  EXPECT_TRUE(after.IsKnown());
  EXPECT_TRUE(after.IsZero() || after.IsOne());
}

TEST(NotifierUpdate, ZRemainsZ) {
  Logic4Word before{1, 1};
  auto after = ToggleNotifierOnViolation(before);
  EXPECT_EQ(after.aval, 1u);
  EXPECT_EQ(after.bval, 1u);
}

// §31.6 states that the notifier (the optional argument declared in each
// check's syntax, e.g. §31.3.1 Syntax 31-3) toggles whenever the timing check
// detects a violation. These two tests weave the two clauses together: the
// §31.3.1 $setup window decision (CheckSetupViolation) gates the §31.6 toggle
// (ToggleNotifierOnViolation) applied to the shared notifier value.

TimingCheckEntry MakeSetupCheck(uint64_t limit) {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kSetup;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.limit = limit;
  return tc;
}

TEST(NotifierUpdate, SetupViolationTogglesNotifier) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetupCheck(10));
  // Data transitions strictly inside the $setup window, so §31.3.1 reports a
  // violation; §31.6 then toggles the notifier from 1 to 0.
  bool violated = mgr.CheckSetupViolation("clk", 100, "data", 95);
  ASSERT_TRUE(violated);
  Logic4Word notifier{1, 0};
  if (violated) notifier = ToggleNotifierOnViolation(notifier);
  EXPECT_TRUE(notifier.IsZero());
}

TEST(NotifierUpdate, NoSetupViolationLeavesNotifierUnchanged) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetupCheck(10));
  // Data transitions on the window's end endpoint, which §31.3.1 excludes from
  // the violation region, so no violation is reported and the notifier is not
  // updated.
  bool violated = mgr.CheckSetupViolation("clk", 100, "data", 100);
  ASSERT_FALSE(violated);
  Logic4Word notifier{1, 0};
  if (violated) notifier = ToggleNotifierOnViolation(notifier);
  EXPECT_TRUE(notifier.IsOne());
}

}  // namespace
