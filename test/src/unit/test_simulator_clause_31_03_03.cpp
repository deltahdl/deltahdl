#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/specify.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Register a `$setuphold` timing check with ref = clk, data = data, and the
// given setup / hold limits written into `limit` / `limit2` respectively.
TimingCheckEntry MakeSetuphold(uint64_t setup_limit, uint64_t hold_limit) {
  TimingCheckEntry tc;
  tc.kind = TimingCheckKind::kSetuphold;
  tc.ref_signal = "clk";
  tc.data_signal = "data";
  tc.limit = setup_limit;
  tc.limit2 = hold_limit;
  return tc;
}

// Data event before the reference edge picks the setup-side window
// (ref_time - setup_limit, ref_time]. A timestamp strictly inside the
// interior (94 in (90, 100]) reports a violation.
TEST(SetupholdTimingCheckWindow, DataFirstStrictlyInsideViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetuphold(10, 5));
  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 94));
}

// §31.3.3: "Only the beginning of the time window is not part of the
// violation region" for the data-event-first case. Begin = ref - setup.
TEST(SetupholdTimingCheckWindow, DataFirstBeginEndpointExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetuphold(10, 5));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 90));
}

// §31.3.3: in the data-first case the end of the window (= ref_time itself)
// is inclusive, so simultaneous events violate while setup > 0.
TEST(SetupholdTimingCheckWindow, DataFirstEndEndpointIncluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetuphold(10, 5));
  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 100));
}

// A timestamp strictly before the setup window is outside the region.
TEST(SetupholdTimingCheckWindow, DataFirstBeforeWindowDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetuphold(10, 5));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 85));
}

// Data event after the reference edge picks the hold-side window
// [ref_time, ref_time + hold_limit). Interior violates.
TEST(SetupholdTimingCheckWindow, DataSecondStrictlyInsideViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetuphold(10, 5));
  EXPECT_TRUE(mgr.CheckSetupholdViolation("clk", 100, "data", 103));
}

// §31.3.3: in the data-second case only the end of the window is excluded.
// End = ref + hold.
TEST(SetupholdTimingCheckWindow, DataSecondEndEndpointExcluded) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetuphold(10, 5));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 105));
}

// A timestamp strictly after the hold window is outside the region.
TEST(SetupholdTimingCheckWindow, DataSecondAfterWindowDoesNotViolate) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetuphold(10, 5));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 110));
}

// Re-run the interior and endpoint cases at different setup and hold limits
// to pin down that each window scales with its respective limit rather than
// a shared constant. Setup=3 shrinks the setup window to (97, 100]; hold=7
// widens the hold window to [100, 107).
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

// §31.3.3: when both limits are zero, `$setuphold` shall never issue a
// violation. Exercises the simultaneous case that would otherwise be most
// suspect.
TEST(SetupholdTimingCheckWindow, BothLimitsZeroNeverViolates) {
  SpecifyManager mgr;
  mgr.AddTimingCheck(MakeSetuphold(0, 0));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 100));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 99));
  EXPECT_FALSE(mgr.CheckSetupholdViolation("clk", 100, "data", 101));
}

// Moved from A.7.5.1: a registered `$setuphold` entry preserves its kind,
// both limits, and notifier when retrieved from the manager.
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

// Moved from A.7.5.1: the full Syntax 31-5 invocation with notifier,
// delayed_reference, and delayed_data drives end-to-end elaboration and
// simulation without disturbing surrounding procedural code.
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

// §31.3.3 explicitly accepts negative limit values. End-to-end simulation
// with both limits negative must run without disturbing procedural code.
TEST(TimingCheckCommandSim, SetupholdNegativeLimitsSimulate) {
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

}  // namespace
