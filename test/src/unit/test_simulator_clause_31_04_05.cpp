#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(TimingCheckCommandSim, PeriodEntryStored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kPeriod;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit = 50;
  mgr.AddTimingCheck(tc);
  ASSERT_EQ(mgr.TimingCheckCount(), 1u);
  const auto& stored = mgr.GetTimingChecks()[0];
  EXPECT_EQ(stored.kind, TimingCheckKind::kPeriod);
  EXPECT_EQ(stored.ref_signal, "clk");
  EXPECT_EQ(stored.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_TRUE(stored.data_signal.empty());
  EXPECT_EQ(stored.limit, 50u);
}

TEST(TimingCheckCommandSim, PeriodElapsedBelowLimitViolates) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kPeriod;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit = 50;
  mgr.AddTimingCheck(tc);

  EXPECT_TRUE(mgr.CheckPeriodViolation("clk", 100, 130));
}

TEST(TimingCheckCommandSim, PeriodElapsedAtLimitNoViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kPeriod;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit = 50;
  mgr.AddTimingCheck(tc);
  EXPECT_FALSE(mgr.CheckPeriodViolation("clk", 100, 150));
}

TEST(TimingCheckCommandSim, PeriodSimultaneousNoViolation) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kPeriod;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit = 50;
  mgr.AddTimingCheck(tc);
  EXPECT_FALSE(mgr.CheckPeriodViolation("clk", 100, 100));
}

TEST(TimingCheckCommandSim, PeriodMismatchedSignalIgnored) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kPeriod;
  tc.ref_signal = "clk";
  tc.ref_edge = SpecifyEdge::kPosedge;
  tc.limit = 50;
  mgr.AddTimingCheck(tc);
  EXPECT_FALSE(mgr.CheckPeriodViolation("other", 100, 130));
}

TEST(TimingCheckCommandSim, PeriodOtherKindsIgnored) {
  SpecifyManager mgr;
  TimingCheckEntry width;
  width.kind = TimingCheckKind::kWidth;
  width.ref_signal = "clk";
  width.limit = 50;
  mgr.AddTimingCheck(width);
  EXPECT_FALSE(mgr.CheckPeriodViolation("clk", 100, 130));
}

TEST(TimingCheckCommandSim, PeriodSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $period(posedge clk, 50);\n"
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

}  // namespace
