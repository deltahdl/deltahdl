#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TimingCheckEntry MakeHold(uint64_t limit) {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kHold;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.limit = limit;
  return tc;
}

TEST(HoldTimingCheckWindow, TimecheckStrictlyInsideViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeHold(5));
  EXPECT_TRUE(mgr.CheckHoldViolation("clk", 100, "data", 103));
}

TEST(HoldTimingCheckWindow, BeginEndpointIncluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeHold(5));
  EXPECT_TRUE(mgr.CheckHoldViolation("clk", 100, "data", 100));
}

TEST(HoldTimingCheckWindow, EndEndpointExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeHold(5));
  EXPECT_FALSE(mgr.CheckHoldViolation("clk", 100, "data", 105));
}

TEST(HoldTimingCheckWindow, TimecheckBeforeRefDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeHold(5));
  EXPECT_FALSE(mgr.CheckHoldViolation("clk", 100, "data", 95));
}

TEST(HoldTimingCheckWindow, TimecheckAfterWindowDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeHold(5));
  EXPECT_FALSE(mgr.CheckHoldViolation("clk", 100, "data", 110));
}

TEST(HoldTimingCheckWindow, WindowScalesWithLimit) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeHold(3));
  EXPECT_FALSE(mgr.CheckHoldViolation("clk", 100, "data", 99));
  EXPECT_TRUE(mgr.CheckHoldViolation("clk", 100, "data", 100));
  EXPECT_TRUE(mgr.CheckHoldViolation("clk", 100, "data", 101));
  EXPECT_TRUE(mgr.CheckHoldViolation("clk", 100, "data", 102));
  EXPECT_FALSE(mgr.CheckHoldViolation("clk", 100, "data", 103));
}

TEST(HoldTimingCheckWindow, ZeroLimitNeverViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeHold(0));
  EXPECT_FALSE(mgr.CheckHoldViolation("clk", 100, "data", 100));
  EXPECT_FALSE(mgr.CheckHoldViolation("clk", 100, "data", 99));
  EXPECT_FALSE(mgr.CheckHoldViolation("clk", 100, "data", 101));
}

TEST(SystemTimingCheckSim, HoldEntryStored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kHold;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.limit = 5;
  mgr.AddTimingCheck(tc);
  EXPECT_EQ(mgr.GetTimingChecks()[0].kind, TimingCheckKind::kHold);
}

TEST(SystemTimingCheckSim, HoldSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $hold(posedge clk, data, 5);\n"
      "  endspecify\n"
      "  initial x = 8'd42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

}
