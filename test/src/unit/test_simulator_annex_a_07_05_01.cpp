#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SystemTimingCheckSim, RuntimeAllTwelveKinds) {
  SpecifyManager mgr;
  TimingCheckKind kinds[] = {
      TimingCheckKind::kSetup,     TimingCheckKind::kHold,
      TimingCheckKind::kSetuphold, TimingCheckKind::kRecovery,
      TimingCheckKind::kRemoval,   TimingCheckKind::kRecrem,
      TimingCheckKind::kSkew,      TimingCheckKind::kTimeskew,
      TimingCheckKind::kFullskew,  TimingCheckKind::kPeriod,
      TimingCheckKind::kWidth,     TimingCheckKind::kNochange,
  };
  for (auto kind : kinds) {
    TimingCheckEntry tc;
    tc.kind = kind;
    tc.ref_signal = "clk";
    tc.data_signal = "data";
    tc.limit = 10;
    mgr.AddTimingCheck(tc);
  }
  EXPECT_EQ(mgr.TimingCheckCount(), 12u);
  for (uint32_t i = 0; i < 12; ++i) {
    EXPECT_EQ(mgr.GetTimingChecks()[i].kind, kinds[i]);
  }
}

TEST(SystemTimingCheckSim, SetupEntryStored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kSetup;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.limit = 10;
  mgr.AddTimingCheck(tc);
  EXPECT_EQ(mgr.TimingCheckCount(), 1u);
  EXPECT_EQ(mgr.GetTimingChecks()[0].kind, TimingCheckKind::kSetup);
}

TEST(SystemTimingCheckSim, SetupSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $setup(data, posedge clk, 10);\n"
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

TEST(SystemTimingCheckSim, TimingChecksWithPathsSimulate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "    $setup(d, posedge clk, 10);\n"
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

TEST(TimingCheckCommandSim, FullskewDualLimitsStored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kFullskew;
  tc.ref_signal = "clk1";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "clk2";
  tc.data_edge = SpecifyEdge::kNegedge;
  tc.limit = 4;
  tc.limit2 = 6;
  mgr.AddTimingCheck(tc);
  auto& stored = mgr.GetTimingChecks()[0];
  EXPECT_EQ(stored.kind, TimingCheckKind::kFullskew);
  EXPECT_EQ(stored.limit, 4u);
  EXPECT_EQ(stored.limit2, 6u);
}

TEST(TimingCheckCommandSim, WidthThresholdAsLimit2) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kWidth;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit = 20;
  tc.limit2 = 1;
  mgr.AddTimingCheck(tc);
  auto& stored = mgr.GetTimingChecks()[0];
  EXPECT_EQ(stored.kind, TimingCheckKind::kWidth);
  EXPECT_EQ(stored.limit, 20u);
  EXPECT_EQ(stored.limit2, 1u);
}

TEST(TimingCheckCommandSim, NochangeOffsetsStored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kNochange;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "data";
  tc.limit = 0;
  tc.limit2 = 0;
  mgr.AddTimingCheck(tc);
  auto& stored = mgr.GetTimingChecks()[0];
  EXPECT_EQ(stored.kind, TimingCheckKind::kNochange);
}

TEST(SystemTimingCheckSim, HoldViolationDetected) {
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

TEST(TimingCheckCommandSim, TimeskewWithFlagsSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $timeskew(posedge clk1, posedge clk2, 5, ntfr, 1, 0);\n"
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

TEST(SystemTimingCheckSim, PeriodEntryNoDataSignal) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kPeriod;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit = 50;
  mgr.AddTimingCheck(tc);
  auto& stored = mgr.GetTimingChecks()[0];
  EXPECT_EQ(stored.kind, TimingCheckKind::kPeriod);
  EXPECT_EQ(stored.ref_signal, "clk");
  EXPECT_TRUE(stored.data_signal.empty());
  EXPECT_EQ(stored.limit, 50u);
}

TEST(SystemTimingCheckSim, WidthEntryNoDataSignal) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kWidth;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit = 20;
  tc.limit2 = 1;
  mgr.AddTimingCheck(tc);
  auto& stored = mgr.GetTimingChecks()[0];
  EXPECT_EQ(stored.kind, TimingCheckKind::kWidth);
  EXPECT_EQ(stored.ref_signal, "clk");
  EXPECT_TRUE(stored.data_signal.empty());
  EXPECT_EQ(stored.limit, 20u);
  EXPECT_EQ(stored.limit2, 1u);
}

TEST(SystemTimingCheckSim, SkewEntryStored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kSkew;
  tc.ref_signal = "clk1";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.data_signal = "clk2";
  tc.data_edge = SpecifyEdge::kNegedge;
  tc.limit = 3;
  mgr.AddTimingCheck(tc);
  auto& stored = mgr.GetTimingChecks()[0];
  EXPECT_EQ(stored.kind, TimingCheckKind::kSkew);
  EXPECT_EQ(stored.ref_signal, "clk1");
  EXPECT_EQ(stored.data_signal, "clk2");
  EXPECT_EQ(stored.limit, 3u);
}

}  // namespace
