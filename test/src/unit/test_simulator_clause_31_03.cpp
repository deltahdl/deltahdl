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

  EXPECT_TRUE(mgr.CheckSetupViolation("clk", 100, "data", 95));

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

  EXPECT_TRUE(mgr.CheckHoldViolation("clk", 100, "data", 103));

  EXPECT_FALSE(mgr.CheckHoldViolation("clk", 100, "data", 110));
}

}  // namespace
