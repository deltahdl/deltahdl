#include <gtest/gtest.h>

#include <cstdint>

#include "common/types.h"
#include "parser/ast_specify.h"
#include "simulator/specify.h"
#include "simulator/specify_timing_check.h"

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
  Logic4Word before{1, 1};
  auto after = ToggleNotifierOnViolation(before);
  EXPECT_TRUE(after.IsKnown());
  EXPECT_TRUE(after.IsZero() || after.IsOne());
}

TEST(NotifierUpdate, ZRemainsZ) {
  Logic4Word before{0, 1};
  auto after = ToggleNotifierOnViolation(before);
  EXPECT_EQ(after.aval, 0u);
  EXPECT_EQ(after.bval, 1u);
}

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
  bool violated = mgr.CheckSetupViolation("clk", 100, "data", 95);
  ASSERT_TRUE(violated);
  Logic4Word notifier{1, 0};
  if (violated) notifier = ToggleNotifierOnViolation(notifier);
  EXPECT_TRUE(notifier.IsZero());
}

TEST(NotifierUpdate, NoSetupViolationLeavesNotifierUnchanged) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetupCheck(10));
  bool violated = mgr.CheckSetupViolation("clk", 100, "data", 100);
  ASSERT_FALSE(violated);
  Logic4Word notifier{1, 0};
  if (violated) notifier = ToggleNotifierOnViolation(notifier);
  EXPECT_TRUE(notifier.IsOne());
}

}  // namespace
