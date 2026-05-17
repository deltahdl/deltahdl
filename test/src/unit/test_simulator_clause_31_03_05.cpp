#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TimingCheckEntry MakeRecovery(uint64_t limit) {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kRecovery;
  tc.ref_signal = "rst";
  tc.data_signal = "clk";
  tc.limit = limit;
  return tc;
}

TEST(RecoveryTimingCheckWindow, TimecheckStrictlyInsideViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecovery(5));
  EXPECT_TRUE(mgr.CheckRecoveryViolation("rst", 100, "clk", 103));
}

TEST(RecoveryTimingCheckWindow, BeginEndpointIncluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecovery(5));
  EXPECT_TRUE(mgr.CheckRecoveryViolation("rst", 100, "clk", 100));
}

TEST(RecoveryTimingCheckWindow, EndEndpointExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecovery(5));
  EXPECT_FALSE(mgr.CheckRecoveryViolation("rst", 100, "clk", 105));
}

TEST(RecoveryTimingCheckWindow, TimecheckBeforeRefDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecovery(5));
  EXPECT_FALSE(mgr.CheckRecoveryViolation("rst", 100, "clk", 95));
}

TEST(RecoveryTimingCheckWindow, TimecheckAfterWindowDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecovery(5));
  EXPECT_FALSE(mgr.CheckRecoveryViolation("rst", 100, "clk", 110));
}

TEST(RecoveryTimingCheckWindow, WindowScalesWithLimit) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecovery(3));
  EXPECT_FALSE(mgr.CheckRecoveryViolation("rst", 100, "clk", 99));
  EXPECT_TRUE(mgr.CheckRecoveryViolation("rst", 100, "clk", 100));
  EXPECT_TRUE(mgr.CheckRecoveryViolation("rst", 100, "clk", 101));
  EXPECT_TRUE(mgr.CheckRecoveryViolation("rst", 100, "clk", 102));
  EXPECT_FALSE(mgr.CheckRecoveryViolation("rst", 100, "clk", 103));
}

TEST(RecoveryTimingCheckWindow, ZeroLimitNeverViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecovery(0));
  EXPECT_FALSE(mgr.CheckRecoveryViolation("rst", 100, "clk", 100));
  EXPECT_FALSE(mgr.CheckRecoveryViolation("rst", 100, "clk", 99));
  EXPECT_FALSE(mgr.CheckRecoveryViolation("rst", 100, "clk", 101));
}

TEST(SystemTimingCheckSim, RecoverySimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $recovery(posedge rst, posedge clk, 5);\n"
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
