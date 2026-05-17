#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TimingCheckEntry MakeRecrem(uint64_t recovery_limit, uint64_t removal_limit) {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kRecrem;
  tc.ref_signal = "clk";
  tc.data_signal = "rst";
  tc.limit = recovery_limit;
  tc.limit2 = removal_limit;
  return tc;
}

TEST(RecremTimingCheckWindow, DataFirstStrictlyInsideViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecrem(8, 4));
  EXPECT_TRUE(mgr.CheckRecremViolation("clk", 100, "rst", 97));
}

TEST(RecremTimingCheckWindow, DataFirstBeginEndpointExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecrem(8, 4));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 96));
}

TEST(RecremTimingCheckWindow, DataFirstEndEndpointIncluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecrem(8, 4));
  EXPECT_TRUE(mgr.CheckRecremViolation("clk", 100, "rst", 100));
}

TEST(RecremTimingCheckWindow, DataFirstBeforeWindowDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecrem(8, 4));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 90));
}

TEST(RecremTimingCheckWindow, DataSecondStrictlyInsideViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecrem(8, 4));
  EXPECT_TRUE(mgr.CheckRecremViolation("clk", 100, "rst", 105));
}

TEST(RecremTimingCheckWindow, DataSecondEndEndpointExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecrem(8, 4));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 108));
}

TEST(RecremTimingCheckWindow, DataSecondAfterWindowDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecrem(8, 4));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 115));
}

TEST(RecremTimingCheckWindow, WindowsScaleWithLimits) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecrem(7, 3));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 96));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 97));
  EXPECT_TRUE(mgr.CheckRecremViolation("clk", 100, "rst", 98));
  EXPECT_TRUE(mgr.CheckRecremViolation("clk", 100, "rst", 100));
  EXPECT_TRUE(mgr.CheckRecremViolation("clk", 100, "rst", 106));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 107));
}

TEST(RecremTimingCheckWindow, BothLimitsZeroNeverViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeRecrem(0, 0));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 100));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 99));
  EXPECT_FALSE(mgr.CheckRecremViolation("clk", 100, "rst", 101));
}

TEST(TimingCheckCommandSim, RecremDualLimitsStored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kRecrem;
  tc.ref_signal = "clk";
  tc.data_signal = "rst";
  tc.limit = 8;
  tc.limit2 = 3;
  mgr.AddTimingCheck(tc);
  auto& stored = mgr.GetTimingChecks()[0];
  EXPECT_EQ(stored.kind, TimingCheckKind::kRecrem);
  EXPECT_EQ(stored.limit, 8u);
  EXPECT_EQ(stored.limit2, 3u);
}

TEST(SystemTimingCheckSim, RecremSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $recrem(posedge clk, rst, 8, 3);\n"
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

TEST(TimingCheckCommandSim, RecremFullArgsSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $recrem(posedge clk, rst, 8, 3, ntfr, , , dCLK, dRST);\n"
      "  endspecify\n"
      "  initial x = 8'd77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

}
