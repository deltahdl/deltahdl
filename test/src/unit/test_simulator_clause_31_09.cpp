#include "common/types.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

#include <gtest/gtest.h>

using namespace delta;

namespace {

TimingCheckEntry MakeSignedSetuphold(int64_t setup, int64_t hold) {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kSetuphold;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.negative_timing_check_enabled = true;
  tc.signed_limit = setup;
  tc.signed_limit2 = hold;
  return tc;
}

TimingCheckEntry MakeSignedRecrem(int64_t recovery, int64_t removal) {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kRecrem;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.negative_timing_check_enabled = true;
  tc.signed_limit = recovery;
  tc.signed_limit2 = removal;
  return tc;
}

TEST(NegativeTimingChecks, NegativeSetupShiftsWindowAfterReference) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSignedSetuphold( -5, 10));

  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 107));
}

TEST(NegativeTimingChecks, NegativeSetupExcludesReferenceEdge) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSignedSetuphold( -5, 10));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 100));
}

TEST(NegativeTimingChecks, NegativeSetupExcludesGapBeforeWindow) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSignedSetuphold( -5, 10));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 103));
}

TEST(NegativeTimingChecks, NegativeHoldShiftsWindowBeforeReference) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSignedSetuphold( 10, -3));

  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 94));
}

TEST(NegativeTimingChecks, NegativeHoldExcludesReferenceEdge) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSignedSetuphold( 10, -3));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 100));
}

TEST(NegativeTimingChecks, BothSignedLimitsZeroNeverViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSignedSetuphold( 0, 0));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 100));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 99));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 101));
}

TEST(NegativeTimingChecks, PositiveSignedLimitsStraddleReference) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSignedSetuphold( 10, 5));

  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 94));
  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 100));
  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 103));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 90));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 105));
}

TEST(NegativeTimingChecks, SetupholdAndRecremAgreeForIdenticalSignedLimits) {
  struct Case {
    int64_t setup;
    int64_t hold;
  };
  const Case cases[] = {
      {-5, 10},
      {10, -3},
      {10, 5},
      {0, 0},
  };
  const uint64_t ref_time = 100;
  for (const auto& c : cases) {
    SpecifyManager mgr_sh;
    SpecifyManager mgr_rr;
    mgr_sh.AddTimingCheck(MakeSignedSetuphold(c.setup, c.hold));
    mgr_rr.AddTimingCheck(MakeSignedRecrem(c.setup, c.hold));
    for (uint64_t t = 88; t <= 112; ++t) {
      const bool sh_viol =
          mgr_sh.CheckSetupholdViolation("clk", ref_time, "data", t);
      const bool rr_viol =
          mgr_rr.CheckRecremViolation("clk", ref_time, "data", t);
      EXPECT_EQ(sh_viol, rr_viol)
          << "setup=" << c.setup << " hold=" << c.hold << " t=" << t;
    }
  }
}

TEST(NegativeTimingChecks, FlagOffPreservesUnsignedSemantics) {
  SpecifyManager mgr;
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kSetuphold;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.limit = 10;
  tc.limit2 = 5;

  tc.signed_limit = -5;
  tc.signed_limit2 = 10;
  tc.negative_timing_check_enabled = false;
  mgr.AddTimingCheck(std::move(tc));

  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 96));

  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 90));
}

TEST(NegativeTimingChecks, SetupholdNegativeLimitsSimulate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $setuphold(posedge clk, data, -10, -5);\n"
      "  endspecify\n"
      "  initial x = 8'd17;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 17u);
}

TEST(NegativeTimingChecks, RecremNegativeLimitsSimulate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  specify\n"
      "    $recrem(posedge clk, rst, -8, -3);\n"
      "  endspecify\n"
      "  initial x = 8'd17;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 17u);
}

}
