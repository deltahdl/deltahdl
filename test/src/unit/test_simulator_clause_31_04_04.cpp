#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(TimingCheckCommandSim, WidthEntryStored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kWidth;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit = 20;
  tc.threshold = 1;
  mgr.AddTimingCheck(tc);
  ASSERT_EQ(mgr.TimingCheckCount(), 1u);
  const auto& stored = mgr.GetTimingChecks()[0];
  EXPECT_EQ(stored.kind, TimingCheckKind::kWidth);
  EXPECT_EQ(stored.ref_signal, "clk");
  EXPECT_EQ(stored.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_TRUE(stored.data_signal.empty());
  EXPECT_EQ(stored.limit, 20u);
  EXPECT_EQ(stored.threshold, 1u);
}

TEST(TimingCheckCommandSim, WidthThresholdDefaultsToZero) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kWidth;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit = 20;
  mgr.AddTimingCheck(tc);
  EXPECT_EQ(mgr.GetTimingChecks()[0].threshold, 0u);
}

TEST(TimingCheckCommandSim, WidthElapsedBetweenThresholdAndLimitViolates) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kWidth;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit = 20;
  tc.threshold = 1;
  mgr.AddTimingCheck(tc);

  EXPECT_TRUE(mgr.CheckWidthViolation("clk", 100, 110));
}

TEST(TimingCheckCommandSim, WidthElapsedAtLimitNoViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kWidth;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit = 20;
  mgr.AddTimingCheck(tc);
  EXPECT_FALSE(mgr.CheckWidthViolation("clk", 100, 120));
}

TEST(TimingCheckCommandSim, WidthElapsedAtThresholdNoViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kWidth;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit = 20;
  tc.threshold = 5;
  mgr.AddTimingCheck(tc);
  EXPECT_FALSE(mgr.CheckWidthViolation("clk", 100, 105));
}

TEST(TimingCheckCommandSim, WidthSimultaneousNoViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kWidth;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit = 20;
  mgr.AddTimingCheck(tc);
  EXPECT_FALSE(mgr.CheckWidthViolation("clk", 100, 100));
}

TEST(TimingCheckCommandSim, WidthMismatchedSignalIgnored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kWidth;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit = 20;
  mgr.AddTimingCheck(tc);
  EXPECT_FALSE(mgr.CheckWidthViolation("other", 100, 110));
}

TEST(TimingCheckCommandSim, WidthOtherKindsIgnored) {
  SpecifyManager mgr;
  TimingCheckEntry setup;
  setup.kind = TimingCheckKind::kSetup;
  setup.ref_signal = "clk";
  setup.data_signal = "data";
  setup.limit = 20;
  mgr.AddTimingCheck(setup);
  EXPECT_FALSE(mgr.CheckWidthViolation("clk", 100, 110));
}

TEST(TimingCheckCommandSim, WidthSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $width(posedge clk, 20, 1);\n"
      "  endspecify\n"
      "  initial x = 8'd55;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

}  // namespace
