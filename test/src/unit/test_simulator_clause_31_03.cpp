// §31.3: Timing checks using a stability window

#include "fixture_specify.h"
#include "simulator/specify.h"

namespace {

TEST_F(SpecifyTest, RuntimeTimingCheckSetupViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kSetup;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.limit = 10;
  mgr.AddTimingCheck(tc);

  // data_time=95, ref_time=100: gap=5 < 10 => violation
  EXPECT_TRUE(mgr.CheckSetupViolation("clk", 100, "data", 95));
  // data_time=85, ref_time=100: gap=15 >= 10 => no violation
  EXPECT_FALSE(mgr.CheckSetupViolation("clk", 100, "data", 85));
}

TEST_F(SpecifyTest, RuntimeTimingCheckHoldViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kHold;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.limit = 5;
  mgr.AddTimingCheck(tc);

  // ref_time=100, data_time=103: gap=3 < 5 => violation
  EXPECT_TRUE(mgr.CheckHoldViolation("clk", 100, "data", 103));
  // ref_time=100, data_time=110: gap=10 >= 5 => no violation
  EXPECT_FALSE(mgr.CheckHoldViolation("clk", 100, "data", 110));
}

}  // namespace
