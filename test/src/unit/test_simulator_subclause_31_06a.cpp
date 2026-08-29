// §31.6's Table 31-13 asked as a function rather than through a run: what a
// timing violation does to a notifier whose value before the violation is x, 0,
// 1 or z. One case per row calls ToggleNotifierOnViolation
// (simulator/specify_timing_check.h) with that row's BEFORE value as a
// Logic4Word and asserts the row's AFTER value. Two further cases call
// SpecifyManager::CheckSetupViolation for the §31.3.1 window decision and apply
// the §31.6 toggle only where that call reports a violation.
//
// No case here writes a design or runs the simulator, which is what separates
// this file from test_simulator_subclause_31_06b.cpp beside it: every case
// there drives a design whose timing check names a notifier variable and reads
// that variable back off the run.
//
// XResolvesToKnownScalar and ZRemainsZ are the regression coverage for issue
// #3413. Each had its four-state encoding crossed against its name: the x case
// built (aval 0, bval 1), which is z, and the z case built (aval 1, bval 1),
// which is x. Each therefore asserted what ToggleNotifierOnViolation did rather
// than what Table 31-13 says, and both rows passed while the function answered
// x for x and 0 for z.
//
// The encoding Logic4Word (common/types.h) carries is (aval, bval): 0 is
// (0, 0), 1 is (1, 0), x is (1, 1) and z is (0, 1).

#include <gtest/gtest.h>

#include "common/types.h"
#include "simulator/specify.h"

using namespace delta;

namespace {

// Table 31-13, second row: BEFORE 0, AFTER 1.
TEST(NotifierUpdate, ZeroTogglesToOne) {
  Logic4Word before{0, 0};
  auto after = ToggleNotifierOnViolation(before);
  EXPECT_TRUE(after.IsOne());
}

// Table 31-13, third row: BEFORE 1, AFTER 0.
TEST(NotifierUpdate, OneTogglesToZero) {
  Logic4Word before{1, 0};
  auto after = ToggleNotifierOnViolation(before);
  EXPECT_TRUE(after.IsZero());
}

// Table 31-13, first row: BEFORE x, AFTER "Either 0 or 1". That row grants a
// licence rather than naming a value, so a conforming answer is 0 and a
// conforming answer is 1. The case asserts the disjunction, which is the whole
// of what the row decides. Asserting the 1 that ToggleNotifierOnViolation
// (simulator/specify_timing_violation.cpp) returns today would pin the choice
// §31.6 leaves open. Such a test passes for as long as the implementation does
// not change and says nothing about the standard.
TEST(NotifierUpdate, XResolvesToKnownScalar) {
  Logic4Word before{1, 1};
  auto after = ToggleNotifierOnViolation(before);
  // Neither x nor z comes back: bval is clear.
  EXPECT_TRUE(after.IsKnown());
  EXPECT_TRUE(after.IsZero() || after.IsOne());
}

// Table 31-13, fourth row: BEFORE z, AFTER z. Both halves of the encoding are
// asserted because z is exactly (aval 0, bval 1); IsKnown() alone would accept
// x, whose bval is set too.
TEST(NotifierUpdate, ZRemainsZ) {
  Logic4Word before{0, 1};
  auto after = ToggleNotifierOnViolation(before);
  EXPECT_EQ(after.aval, 0u);
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
  // violation; Table 31-13's third row then takes the notifier from 1 to 0.
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
  // updated. Table 31-13 applies to a violation only, so the 1 stands.
  bool violated = mgr.CheckSetupViolation("clk", 100, "data", 100);
  ASSERT_FALSE(violated);
  Logic4Word notifier{1, 0};
  if (violated) notifier = ToggleNotifierOnViolation(notifier);
  EXPECT_TRUE(notifier.IsOne());
}

}  // namespace
