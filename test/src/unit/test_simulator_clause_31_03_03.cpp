#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TimingCheckEntry MakeSetuphold(uint64_t setup_limit, uint64_t hold_limit) {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kSetuphold;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.limit = setup_limit;
  tc.limit2 = hold_limit;
  return tc;
}

TEST(SetupholdTimingCheckWindow, DataFirstStrictlyInsideViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetuphold(10, 5));
  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 94));
}

TEST(SetupholdTimingCheckWindow, DataFirstBeginEndpointExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetuphold(10, 5));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 90));
}

TEST(SetupholdTimingCheckWindow, DataFirstEndEndpointIncluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetuphold(10, 5));
  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 100));
}

TEST(SetupholdTimingCheckWindow, DataFirstBeforeWindowDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetuphold(10, 5));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 85));
}

TEST(SetupholdTimingCheckWindow, DataSecondStrictlyInsideViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetuphold(10, 5));
  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 103));
}

TEST(SetupholdTimingCheckWindow, DataSecondEndEndpointExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetuphold(10, 5));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 105));
}

TEST(SetupholdTimingCheckWindow, DataSecondAfterWindowDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetuphold(10, 5));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 110));
}

TEST(SetupholdTimingCheckWindow, WindowsScaleWithLimits) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetuphold(3, 7));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 96));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 97));
  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 98));
  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 100));
  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 106));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 107));
}

TEST(SetupholdTimingCheckWindow, BothLimitsZeroNeverViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetuphold(0, 0));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 100));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 99));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 101));
}

TEST(TimingCheckCommandSim, SetupholdDualLimitsStored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kSetuphold;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.limit = 10;
  tc.limit2 = 5;
  tc.notifier = "ntfr";
  mgr.AddTimingCheck(tc);
  ASSERT_EQ(mgr.TimingCheckCount(), 1u);
  auto& stored = mgr.GetTimingChecks()[0];
  EXPECT_EQ(stored.kind, TimingCheckKind::kSetuphold);
  EXPECT_EQ(stored.limit, 10u);
  EXPECT_EQ(stored.limit2, 5u);
  EXPECT_EQ(stored.notifier, "ntfr");
}

TEST(TimingCheckCommandSim, SetupholdFullArgsSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $setuphold(posedge clk, data, 10, 5, ntfr, , , dCLK, dDATA);\n"
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
