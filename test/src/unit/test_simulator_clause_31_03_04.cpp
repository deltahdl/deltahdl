#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TimingCheckEntry MakeRemoval(uint64_t limit) {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kRemoval;
  tc.ref_signal = "rst";
  tc.data_signal = "clk";
  tc.limit = limit;
  return tc;
}

TEST(RemovalTimingCheckWindow, TimestampStrictlyInsideViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRemoval(10));
  EXPECT_TRUE(mgr.CheckRemovalViolation("rst", 100, "clk", 95));
}

TEST(RemovalTimingCheckWindow, BeginEndpointExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRemoval(10));
  EXPECT_FALSE(mgr.CheckRemovalViolation("rst", 100, "clk", 90));
}

TEST(RemovalTimingCheckWindow, EndEndpointExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRemoval(10));
  EXPECT_FALSE(mgr.CheckRemovalViolation("rst", 100, "clk", 100));
}

TEST(RemovalTimingCheckWindow, TimestampBeforeWindowDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRemoval(10));
  EXPECT_FALSE(mgr.CheckRemovalViolation("rst", 100, "clk", 85));
}

TEST(RemovalTimingCheckWindow, TimestampAfterTimecheckDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRemoval(10));
  EXPECT_FALSE(mgr.CheckRemovalViolation("rst", 100, "clk", 105));
}

TEST(RemovalTimingCheckWindow, WindowScalesWithLimit) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRemoval(3));
  EXPECT_FALSE(mgr.CheckRemovalViolation("rst", 100, "clk", 96));
  EXPECT_FALSE(mgr.CheckRemovalViolation("rst", 100, "clk", 97));
  EXPECT_TRUE(mgr.CheckRemovalViolation("rst", 100, "clk", 98));
  EXPECT_TRUE(mgr.CheckRemovalViolation("rst", 100, "clk", 99));
  EXPECT_FALSE(mgr.CheckRemovalViolation("rst", 100, "clk", 100));
}

TEST(RemovalTimingCheckWindow, ZeroLimitNeverViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRemoval(0));
  EXPECT_FALSE(mgr.CheckRemovalViolation("rst", 100, "clk", 100));
  EXPECT_FALSE(mgr.CheckRemovalViolation("rst", 100, "clk", 99));
  EXPECT_FALSE(mgr.CheckRemovalViolation("rst", 100, "clk", 101));
}

TEST(SystemTimingCheckSim, RemovalSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $removal(posedge rst, posedge clk, 5);\n"
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
