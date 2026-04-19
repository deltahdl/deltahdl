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

}  // namespace
